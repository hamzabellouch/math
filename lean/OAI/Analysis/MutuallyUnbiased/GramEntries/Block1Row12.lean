import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block40
import OAI.Analysis.MutuallyUnbiased.GramRows.Block41
import OAI.Analysis.MutuallyUnbiased.GramRows.Block42
import OAI.Analysis.MutuallyUnbiased.GramRows.Block43

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2086, row2087, row2088, row2089, row2090, row2091, row2092, row2093, row2094, row2095, row2096, row2097, row2098, row2099, row2100, row2101, row2102, row2103, row2104, row2105, row2106, row2107, row2108, row2109, row2110, row2111, row2112, row2113, row2114, row2115]

theorem entryCheck12_0 : entry12_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_0 k)) := by decide +kernel

theorem rowsSound12_0 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval2086 x
  · exact rowEval2087 x
  · exact rowEval2088 x
  · exact rowEval2089 x
  · exact rowEval2090 x
  · exact rowEval2091 x
  · exact rowEval2092 x
  · exact rowEval2093 x
  · exact rowEval2094 x
  · exact rowEval2095 x
  · exact rowEval2096 x
  · exact rowEval2097 x
  · exact rowEval2098 x
  · exact rowEval2099 x
  · exact rowEval2100 x
  · exact rowEval2101 x
  · exact rowEval2102 x
  · exact rowEval2103 x
  · exact rowEval2104 x
  · exact rowEval2105 x
  · exact rowEval2106 x
  · exact rowEval2107 x
  · exact rowEval2108 x
  · exact rowEval2109 x
  · exact rowEval2110 x
  · exact rowEval2111 x
  · exact rowEval2112 x
  · exact rowEval2113 x
  · exact rowEval2114 x
  · exact rowEval2115 x

theorem entryEval12_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_0 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck12_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_0]

def rows12_1 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2116, row2117, row2118, row2119, row2120, row2121, row2122, row2123, row2124, row2125, row2126, row2127, row2128, row2129, row2130, row2131, row2132, row2133, row2134, row2135, row2136, row2137, row2138, row2139, row2140, row2141, row2142, row2143, row2144, row2145]

theorem entryCheck12_1 : entry12_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_1 k)) := by decide +kernel

theorem rowsSound12_1 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2116 x
  · exact rowEval2117 x
  · exact rowEval2118 x
  · exact rowEval2119 x
  · exact rowEval2120 x
  · exact rowEval2121 x
  · exact rowEval2122 x
  · exact rowEval2123 x
  · exact rowEval2124 x
  · exact rowEval2125 x
  · exact rowEval2126 x
  · exact rowEval2127 x
  · exact rowEval2128 x
  · exact rowEval2129 x
  · exact rowEval2130 x
  · exact rowEval2131 x
  · exact rowEval2132 x
  · exact rowEval2133 x
  · exact rowEval2134 x
  · exact rowEval2135 x
  · exact rowEval2136 x
  · exact rowEval2137 x
  · exact rowEval2138 x
  · exact rowEval2139 x
  · exact rowEval2140 x
  · exact rowEval2141 x
  · exact rowEval2142 x
  · exact rowEval2143 x
  · exact rowEval2144 x
  · exact rowEval2145 x

theorem entryEval12_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_1 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck12_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_1]

def rows12_2 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2146, row2147, row2148, row2149, row2150, row2151, row2152, row2153, row2154, row2155, row2156, row2157, row2158, row2159, row2160, row2161, row2162, row2163, row2164, row2165, row2166, row2167, row2168, row2169, row2170, row2171, row2172, row2173, row2174, row2175]

theorem entryCheck12_2 : entry12_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_2 k)) := by decide +kernel

theorem rowsSound12_2 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval2146 x
  · exact rowEval2147 x
  · exact rowEval2148 x
  · exact rowEval2149 x
  · exact rowEval2150 x
  · exact rowEval2151 x
  · exact rowEval2152 x
  · exact rowEval2153 x
  · exact rowEval2154 x
  · exact rowEval2155 x
  · exact rowEval2156 x
  · exact rowEval2157 x
  · exact rowEval2158 x
  · exact rowEval2159 x
  · exact rowEval2160 x
  · exact rowEval2161 x
  · exact rowEval2162 x
  · exact rowEval2163 x
  · exact rowEval2164 x
  · exact rowEval2165 x
  · exact rowEval2166 x
  · exact rowEval2167 x
  · exact rowEval2168 x
  · exact rowEval2169 x
  · exact rowEval2170 x
  · exact rowEval2171 x
  · exact rowEval2172 x
  · exact rowEval2173 x
  · exact rowEval2174 x
  · exact rowEval2175 x

theorem entryEval12_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_2 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck12_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_2]

def rows12_3 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2176, row2177, row2178, row2179, row2180, row2181, row2182, row2183, row2184, row2185, row2186, row2187, row2188, row2189, row2190, row2191, row2192, row2193, row2194, row2195, row2196, row2197, row2198, row2199, row2200, row2201, row2202, row2203, row2204, row2205]

theorem entryCheck12_3 : entry12_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_3 k)) := by decide +kernel

theorem rowsSound12_3 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2176 x
  · exact rowEval2177 x
  · exact rowEval2178 x
  · exact rowEval2179 x
  · exact rowEval2180 x
  · exact rowEval2181 x
  · exact rowEval2182 x
  · exact rowEval2183 x
  · exact rowEval2184 x
  · exact rowEval2185 x
  · exact rowEval2186 x
  · exact rowEval2187 x
  · exact rowEval2188 x
  · exact rowEval2189 x
  · exact rowEval2190 x
  · exact rowEval2191 x
  · exact rowEval2192 x
  · exact rowEval2193 x
  · exact rowEval2194 x
  · exact rowEval2195 x
  · exact rowEval2196 x
  · exact rowEval2197 x
  · exact rowEval2198 x
  · exact rowEval2199 x
  · exact rowEval2200 x
  · exact rowEval2201 x
  · exact rowEval2202 x
  · exact rowEval2203 x
  · exact rowEval2204 x
  · exact rowEval2205 x

theorem entryEval12_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_3 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck12_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_3]

def rows12_4 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2206, row2207, row2208, row2209, row2210, row2211, row2212, row2213, row2214, row2215, row2216, row2217, row2218, row2219, row2220, row2221, row2222, row2223, row2224, row2225, row2226, row2227, row2228, row2229, row2230, row2231, row2232, row2233, row2234, row2235]

theorem entryCheck12_4 : entry12_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_4 k)) := by decide +kernel

theorem rowsSound12_4 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2206 x
  · exact rowEval2207 x
  · exact rowEval2208 x
  · exact rowEval2209 x
  · exact rowEval2210 x
  · exact rowEval2211 x
  · exact rowEval2212 x
  · exact rowEval2213 x
  · exact rowEval2214 x
  · exact rowEval2215 x
  · exact rowEval2216 x
  · exact rowEval2217 x
  · exact rowEval2218 x
  · exact rowEval2219 x
  · exact rowEval2220 x
  · exact rowEval2221 x
  · exact rowEval2222 x
  · exact rowEval2223 x
  · exact rowEval2224 x
  · exact rowEval2225 x
  · exact rowEval2226 x
  · exact rowEval2227 x
  · exact rowEval2228 x
  · exact rowEval2229 x
  · exact rowEval2230 x
  · exact rowEval2231 x
  · exact rowEval2232 x
  · exact rowEval2233 x
  · exact rowEval2234 x
  · exact rowEval2235 x

theorem entryEval12_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_4 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck12_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_4]

def rows12_5 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2236, row2237, row2238, row2239, row2240, row2241, row2242, row2243, row2244, row2245, row2246, row2247, row2248, row2249, row2250, row2251, row2252, row2253, row2254, row2255, row2256, row2257, row2258, row2259, row2260, row2261, row2262, row2263, row2264, row2265]

theorem entryCheck12_5 : entry12_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_5 k)) := by decide +kernel

theorem rowsSound12_5 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2236 x
  · exact rowEval2237 x
  · exact rowEval2238 x
  · exact rowEval2239 x
  · exact rowEval2240 x
  · exact rowEval2241 x
  · exact rowEval2242 x
  · exact rowEval2243 x
  · exact rowEval2244 x
  · exact rowEval2245 x
  · exact rowEval2246 x
  · exact rowEval2247 x
  · exact rowEval2248 x
  · exact rowEval2249 x
  · exact rowEval2250 x
  · exact rowEval2251 x
  · exact rowEval2252 x
  · exact rowEval2253 x
  · exact rowEval2254 x
  · exact rowEval2255 x
  · exact rowEval2256 x
  · exact rowEval2257 x
  · exact rowEval2258 x
  · exact rowEval2259 x
  · exact rowEval2260 x
  · exact rowEval2261 x
  · exact rowEval2262 x
  · exact rowEval2263 x
  · exact rowEval2264 x
  · exact rowEval2265 x

theorem entryEval12_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_5 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck12_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_5]

def rows12_6 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2266, row2267, row2268, row2269, row2270, row2271, row2272, row2273, row2274, row2275, row2276, row2277, row2278, row2279, row2280, row2281, row2282, row2283, row2284, row2285, row2286, row2287, row2288, row2289, row2290, row2291, row2292, row2293, row2294, row2295]

theorem entryCheck12_6 : entry12_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_6 k)) := by decide +kernel

theorem rowsSound12_6 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2266 x
  · exact rowEval2267 x
  · exact rowEval2268 x
  · exact rowEval2269 x
  · exact rowEval2270 x
  · exact rowEval2271 x
  · exact rowEval2272 x
  · exact rowEval2273 x
  · exact rowEval2274 x
  · exact rowEval2275 x
  · exact rowEval2276 x
  · exact rowEval2277 x
  · exact rowEval2278 x
  · exact rowEval2279 x
  · exact rowEval2280 x
  · exact rowEval2281 x
  · exact rowEval2282 x
  · exact rowEval2283 x
  · exact rowEval2284 x
  · exact rowEval2285 x
  · exact rowEval2286 x
  · exact rowEval2287 x
  · exact rowEval2288 x
  · exact rowEval2289 x
  · exact rowEval2290 x
  · exact rowEval2291 x
  · exact rowEval2292 x
  · exact rowEval2293 x
  · exact rowEval2294 x
  · exact rowEval2295 x

theorem entryEval12_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_6 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck12_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_6]

def rows12_7 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2296, row2297, row2298, row2299, row2300, row2301, row2302, row2303, row2304, row2305, row2306, row2307, row2308, row2309, row2310, row2311, row2312, row2313, row2314, row2315, row2316, row2317, row2318, row2319, row2320, row2321, row2322, row2323, row2324, row2325]

theorem entryCheck12_7 : entry12_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_7 k)) := by decide +kernel

theorem rowsSound12_7 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2296 x
  · exact rowEval2297 x
  · exact rowEval2298 x
  · exact rowEval2299 x
  · exact rowEval2300 x
  · exact rowEval2301 x
  · exact rowEval2302 x
  · exact rowEval2303 x
  · exact rowEval2304 x
  · exact rowEval2305 x
  · exact rowEval2306 x
  · exact rowEval2307 x
  · exact rowEval2308 x
  · exact rowEval2309 x
  · exact rowEval2310 x
  · exact rowEval2311 x
  · exact rowEval2312 x
  · exact rowEval2313 x
  · exact rowEval2314 x
  · exact rowEval2315 x
  · exact rowEval2316 x
  · exact rowEval2317 x
  · exact rowEval2318 x
  · exact rowEval2319 x
  · exact rowEval2320 x
  · exact rowEval2321 x
  · exact rowEval2322 x
  · exact rowEval2323 x
  · exact rowEval2324 x
  · exact rowEval2325 x

theorem entryEval12_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_7 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck12_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_7]

def rows12_8 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2326, row2327, row2328, row2329, row2330, row2331, row2332, row2333, row2334, row2335, row2336, row2337, row2338, row2339, row2340, row2341, row2342, row2343, row2344, row2345, row2346, row2347, row2348, row2349, row2350, row2351, row2352, row2353, row2354, row2355]

theorem entryCheck12_8 : entry12_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_8 k)) := by decide +kernel

theorem rowsSound12_8 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2326 x
  · exact rowEval2327 x
  · exact rowEval2328 x
  · exact rowEval2329 x
  · exact rowEval2330 x
  · exact rowEval2331 x
  · exact rowEval2332 x
  · exact rowEval2333 x
  · exact rowEval2334 x
  · exact rowEval2335 x
  · exact rowEval2336 x
  · exact rowEval2337 x
  · exact rowEval2338 x
  · exact rowEval2339 x
  · exact rowEval2340 x
  · exact rowEval2341 x
  · exact rowEval2342 x
  · exact rowEval2343 x
  · exact rowEval2344 x
  · exact rowEval2345 x
  · exact rowEval2346 x
  · exact rowEval2347 x
  · exact rowEval2348 x
  · exact rowEval2349 x
  · exact rowEval2350 x
  · exact rowEval2351 x
  · exact rowEval2352 x
  · exact rowEval2353 x
  · exact rowEval2354 x
  · exact rowEval2355 x

theorem entryEval12_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_8 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck12_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_8]

def rows12_9 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2356, row2357, row2358, row2359, row2360, row2361, row2362, row2363, row2364, row2365, row2366, row2367, row2368, row2369, row2370, row2371, row2372, row2373, row2374, row2375, row2376, row2377, row2378, row2379, row2380, row2381, row2382, row2383, row2384, row2385]

theorem entryCheck12_9 : entry12_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_9 k)) := by decide +kernel

theorem rowsSound12_9 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2356 x
  · exact rowEval2357 x
  · exact rowEval2358 x
  · exact rowEval2359 x
  · exact rowEval2360 x
  · exact rowEval2361 x
  · exact rowEval2362 x
  · exact rowEval2363 x
  · exact rowEval2364 x
  · exact rowEval2365 x
  · exact rowEval2366 x
  · exact rowEval2367 x
  · exact rowEval2368 x
  · exact rowEval2369 x
  · exact rowEval2370 x
  · exact rowEval2371 x
  · exact rowEval2372 x
  · exact rowEval2373 x
  · exact rowEval2374 x
  · exact rowEval2375 x
  · exact rowEval2376 x
  · exact rowEval2377 x
  · exact rowEval2378 x
  · exact rowEval2379 x
  · exact rowEval2380 x
  · exact rowEval2381 x
  · exact rowEval2382 x
  · exact rowEval2383 x
  · exact rowEval2384 x
  · exact rowEval2385 x

theorem entryEval12_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_9 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck12_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_9]

def rows12_10 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2386, row2387, row2388, row2389, row2390, row2391, row2392, row2393, row2394, row2395, row2396, row2397, row2398, row2399, row2400, row2401, row2402, row2403, row2404, row2405, row2406, row2407, row2408, row2409, row2410, row2411, row2412, row2413, row2414, row2415]

theorem entryCheck12_10 : entry12_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_10 k)) := by decide +kernel

theorem rowsSound12_10 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2386 x
  · exact rowEval2387 x
  · exact rowEval2388 x
  · exact rowEval2389 x
  · exact rowEval2390 x
  · exact rowEval2391 x
  · exact rowEval2392 x
  · exact rowEval2393 x
  · exact rowEval2394 x
  · exact rowEval2395 x
  · exact rowEval2396 x
  · exact rowEval2397 x
  · exact rowEval2398 x
  · exact rowEval2399 x
  · exact rowEval2400 x
  · exact rowEval2401 x
  · exact rowEval2402 x
  · exact rowEval2403 x
  · exact rowEval2404 x
  · exact rowEval2405 x
  · exact rowEval2406 x
  · exact rowEval2407 x
  · exact rowEval2408 x
  · exact rowEval2409 x
  · exact rowEval2410 x
  · exact rowEval2411 x
  · exact rowEval2412 x
  · exact rowEval2413 x
  · exact rowEval2414 x
  · exact rowEval2415 x

theorem entryEval12_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_10 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck12_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_10]

def rows12_11 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2416, row2417, row2418, row2419, row2420, row2421, row2422, row2423, row2424, row2425, row2426, row2427, row2428, row2429, row2430, row2431, row2432, row2433, row2434, row2435, row2436, row2437, row2438, row2439, row2440, row2441, row2442, row2443, row2444, row2445]

theorem entryCheck12_11 : entry12_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_11 k)) := by decide +kernel

theorem rowsSound12_11 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2416 x
  · exact rowEval2417 x
  · exact rowEval2418 x
  · exact rowEval2419 x
  · exact rowEval2420 x
  · exact rowEval2421 x
  · exact rowEval2422 x
  · exact rowEval2423 x
  · exact rowEval2424 x
  · exact rowEval2425 x
  · exact rowEval2426 x
  · exact rowEval2427 x
  · exact rowEval2428 x
  · exact rowEval2429 x
  · exact rowEval2430 x
  · exact rowEval2431 x
  · exact rowEval2432 x
  · exact rowEval2433 x
  · exact rowEval2434 x
  · exact rowEval2435 x
  · exact rowEval2436 x
  · exact rowEval2437 x
  · exact rowEval2438 x
  · exact rowEval2439 x
  · exact rowEval2440 x
  · exact rowEval2441 x
  · exact rowEval2442 x
  · exact rowEval2443 x
  · exact rowEval2444 x
  · exact rowEval2445 x

theorem entryEval12_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_11 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck12_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_11]

def rows12_12 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2446, row2447, row2448, row2449, row2450, row2451, row2452, row2453, row2454, row2455, row2456, row2457, row2458, row2459, row2460, row2461, row2462, row2463, row2464, row2465, row2466, row2467, row2468, row2469, row2470, row2471, row2472, row2473, row2474, row2475]

theorem entryCheck12_12 : entry12_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form12.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form12.terms k).coefficient) (rows12_12 k)) := by decide +kernel

theorem rowsSound12_12 (k : Fin GramFunctions.Block1.form12.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows12_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form12.terms k).tag (GramFunctions.Block1.form12.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2446 x
  · exact rowEval2447 x
  · exact rowEval2448 x
  · exact rowEval2449 x
  · exact rowEval2450 x
  · exact rowEval2451 x
  · exact rowEval2452 x
  · exact rowEval2453 x
  · exact rowEval2454 x
  · exact rowEval2455 x
  · exact rowEval2456 x
  · exact rowEval2457 x
  · exact rowEval2458 x
  · exact rowEval2459 x
  · exact rowEval2460 x
  · exact rowEval2461 x
  · exact rowEval2462 x
  · exact rowEval2463 x
  · exact rowEval2464 x
  · exact rowEval2465 x
  · exact rowEval2466 x
  · exact rowEval2467 x
  · exact rowEval2468 x
  · exact rowEval2469 x
  · exact rowEval2470 x
  · exact rowEval2471 x
  · exact rowEval2472 x
  · exact rowEval2473 x
  · exact rowEval2474 x
  · exact rowEval2475 x

theorem entryEval12_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry12_12 (GramNormalization.eval B) = GramFunctions.Block1.form12.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck12_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form12 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound12_12]

end MUB6.Certificate.GramEntries.Block1

end OAI
