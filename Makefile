propcheck : propcheck.cc
	g++ -std=c++0x -DNDEBUG -O3 $< -o $@

.PHONY: clean

clean:
	rm -f propcheck
