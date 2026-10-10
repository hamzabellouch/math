import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block40
import OAI.Analysis.MutuallyUnbiased.GramRows.Block41
import OAI.Analysis.MutuallyUnbiased.GramRows.Block42
import OAI.Analysis.MutuallyUnbiased.GramRows.Block43
import OAI.Analysis.MutuallyUnbiased.GramRows.Block51
import OAI.Analysis.MutuallyUnbiased.GramRows.Block52
import OAI.Analysis.MutuallyUnbiased.GramRows.Block57
import OAI.Analysis.MutuallyUnbiased.GramRows.Block58
import OAI.Analysis.MutuallyUnbiased.GramRows.Block59

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2098, row2099, row2100, row2101, row2102, row2103, row3479, row3480, row3481, row2110, row2111, row2112, row2113, row2114, row2115, row4244, row4245, row4246, row4247, row4248, row4249, row3485, row3486, row3487, row4250, row4251, row4252, row4253, row4254, row4255]

theorem entryCheck18_0 : entry18_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_0 k)) := by decide +kernel

theorem rowsSound18_0 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval2098 x
  · exact rowEval2099 x
  · exact rowEval2100 x
  · exact rowEval2101 x
  · exact rowEval2102 x
  · exact rowEval2103 x
  · exact rowEval3479 x
  · exact rowEval3480 x
  · exact rowEval3481 x
  · exact rowEval2110 x
  · exact rowEval2111 x
  · exact rowEval2112 x
  · exact rowEval2113 x
  · exact rowEval2114 x
  · exact rowEval2115 x
  · exact rowEval4244 x
  · exact rowEval4245 x
  · exact rowEval4246 x
  · exact rowEval4247 x
  · exact rowEval4248 x
  · exact rowEval4249 x
  · exact rowEval3485 x
  · exact rowEval3486 x
  · exact rowEval3487 x
  · exact rowEval4250 x
  · exact rowEval4251 x
  · exact rowEval4252 x
  · exact rowEval4253 x
  · exact rowEval4254 x
  · exact rowEval4255 x

theorem entryEval18_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_0 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck18_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_0]

def rows18_1 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2128, row2129, row2130, row2131, row2132, row2133, row3491, row3492, row3493, row2140, row2141, row2142, row2143, row2144, row2145, row4256, row4257, row4258, row4259, row4260, row4261, row3497, row3498, row3499, row4262, row4263, row4264, row4265, row4266, row4267]

theorem entryCheck18_1 : entry18_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_1 k)) := by decide +kernel

theorem rowsSound18_1 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2128 x
  · exact rowEval2129 x
  · exact rowEval2130 x
  · exact rowEval2131 x
  · exact rowEval2132 x
  · exact rowEval2133 x
  · exact rowEval3491 x
  · exact rowEval3492 x
  · exact rowEval3493 x
  · exact rowEval2140 x
  · exact rowEval2141 x
  · exact rowEval2142 x
  · exact rowEval2143 x
  · exact rowEval2144 x
  · exact rowEval2145 x
  · exact rowEval4256 x
  · exact rowEval4257 x
  · exact rowEval4258 x
  · exact rowEval4259 x
  · exact rowEval4260 x
  · exact rowEval4261 x
  · exact rowEval3497 x
  · exact rowEval3498 x
  · exact rowEval3499 x
  · exact rowEval4262 x
  · exact rowEval4263 x
  · exact rowEval4264 x
  · exact rowEval4265 x
  · exact rowEval4266 x
  · exact rowEval4267 x

theorem entryEval18_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_1 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck18_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_1]

def rows18_2 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2158, row2159, row2160, row2161, row2162, row2163, row3503, row3504, row3505, row2170, row2171, row2172, row2173, row2174, row2175, row4268, row4269, row4270, row4271, row4272, row4273, row3509, row3510, row3511, row4274, row4275, row4276, row4277, row4278, row4279]

theorem entryCheck18_2 : entry18_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_2 k)) := by decide +kernel

theorem rowsSound18_2 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval2158 x
  · exact rowEval2159 x
  · exact rowEval2160 x
  · exact rowEval2161 x
  · exact rowEval2162 x
  · exact rowEval2163 x
  · exact rowEval3503 x
  · exact rowEval3504 x
  · exact rowEval3505 x
  · exact rowEval2170 x
  · exact rowEval2171 x
  · exact rowEval2172 x
  · exact rowEval2173 x
  · exact rowEval2174 x
  · exact rowEval2175 x
  · exact rowEval4268 x
  · exact rowEval4269 x
  · exact rowEval4270 x
  · exact rowEval4271 x
  · exact rowEval4272 x
  · exact rowEval4273 x
  · exact rowEval3509 x
  · exact rowEval3510 x
  · exact rowEval3511 x
  · exact rowEval4274 x
  · exact rowEval4275 x
  · exact rowEval4276 x
  · exact rowEval4277 x
  · exact rowEval4278 x
  · exact rowEval4279 x

theorem entryEval18_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_2 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck18_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_2]

def rows18_3 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2188, row2189, row2190, row2191, row2192, row2193, row3515, row3516, row3517, row2200, row2201, row2202, row2203, row2204, row2205, row4280, row4281, row4282, row4283, row4284, row4285, row3521, row3522, row3523, row4286, row4287, row4288, row4289, row4290, row4291]

theorem entryCheck18_3 : entry18_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_3 k)) := by decide +kernel

theorem rowsSound18_3 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2188 x
  · exact rowEval2189 x
  · exact rowEval2190 x
  · exact rowEval2191 x
  · exact rowEval2192 x
  · exact rowEval2193 x
  · exact rowEval3515 x
  · exact rowEval3516 x
  · exact rowEval3517 x
  · exact rowEval2200 x
  · exact rowEval2201 x
  · exact rowEval2202 x
  · exact rowEval2203 x
  · exact rowEval2204 x
  · exact rowEval2205 x
  · exact rowEval4280 x
  · exact rowEval4281 x
  · exact rowEval4282 x
  · exact rowEval4283 x
  · exact rowEval4284 x
  · exact rowEval4285 x
  · exact rowEval3521 x
  · exact rowEval3522 x
  · exact rowEval3523 x
  · exact rowEval4286 x
  · exact rowEval4287 x
  · exact rowEval4288 x
  · exact rowEval4289 x
  · exact rowEval4290 x
  · exact rowEval4291 x

theorem entryEval18_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_3 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck18_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_3]

def rows18_4 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2218, row2219, row2220, row2221, row2222, row2223, row3527, row3528, row3529, row2230, row2231, row2232, row2233, row2234, row2235, row4292, row4293, row4294, row4295, row4296, row4297, row3533, row3534, row3535, row4298, row4299, row4300, row4301, row4302, row4303]

theorem entryCheck18_4 : entry18_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_4 k)) := by decide +kernel

theorem rowsSound18_4 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2218 x
  · exact rowEval2219 x
  · exact rowEval2220 x
  · exact rowEval2221 x
  · exact rowEval2222 x
  · exact rowEval2223 x
  · exact rowEval3527 x
  · exact rowEval3528 x
  · exact rowEval3529 x
  · exact rowEval2230 x
  · exact rowEval2231 x
  · exact rowEval2232 x
  · exact rowEval2233 x
  · exact rowEval2234 x
  · exact rowEval2235 x
  · exact rowEval4292 x
  · exact rowEval4293 x
  · exact rowEval4294 x
  · exact rowEval4295 x
  · exact rowEval4296 x
  · exact rowEval4297 x
  · exact rowEval3533 x
  · exact rowEval3534 x
  · exact rowEval3535 x
  · exact rowEval4298 x
  · exact rowEval4299 x
  · exact rowEval4300 x
  · exact rowEval4301 x
  · exact rowEval4302 x
  · exact rowEval4303 x

theorem entryEval18_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_4 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck18_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_4]

def rows18_5 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2248, row2249, row2250, row2251, row2252, row2253, row3539, row3540, row3541, row2260, row2261, row2262, row2263, row2264, row2265, row4304, row4305, row4306, row4307, row4308, row4309, row3545, row3546, row3547, row4310, row4311, row4312, row4313, row4314, row4315]

theorem entryCheck18_5 : entry18_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_5 k)) := by decide +kernel

theorem rowsSound18_5 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2248 x
  · exact rowEval2249 x
  · exact rowEval2250 x
  · exact rowEval2251 x
  · exact rowEval2252 x
  · exact rowEval2253 x
  · exact rowEval3539 x
  · exact rowEval3540 x
  · exact rowEval3541 x
  · exact rowEval2260 x
  · exact rowEval2261 x
  · exact rowEval2262 x
  · exact rowEval2263 x
  · exact rowEval2264 x
  · exact rowEval2265 x
  · exact rowEval4304 x
  · exact rowEval4305 x
  · exact rowEval4306 x
  · exact rowEval4307 x
  · exact rowEval4308 x
  · exact rowEval4309 x
  · exact rowEval3545 x
  · exact rowEval3546 x
  · exact rowEval3547 x
  · exact rowEval4310 x
  · exact rowEval4311 x
  · exact rowEval4312 x
  · exact rowEval4313 x
  · exact rowEval4314 x
  · exact rowEval4315 x

theorem entryEval18_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_5 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck18_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_5]

def rows18_6 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2278, row2279, row2280, row2281, row2282, row2283, row3551, row3552, row3553, row2290, row2291, row2292, row2293, row2294, row2295, row4316, row4317, row4318, row4319, row4320, row4321, row3557, row3558, row3559, row4322, row4323, row4324, row4325, row4326, row4327]

theorem entryCheck18_6 : entry18_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_6 k)) := by decide +kernel

theorem rowsSound18_6 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2278 x
  · exact rowEval2279 x
  · exact rowEval2280 x
  · exact rowEval2281 x
  · exact rowEval2282 x
  · exact rowEval2283 x
  · exact rowEval3551 x
  · exact rowEval3552 x
  · exact rowEval3553 x
  · exact rowEval2290 x
  · exact rowEval2291 x
  · exact rowEval2292 x
  · exact rowEval2293 x
  · exact rowEval2294 x
  · exact rowEval2295 x
  · exact rowEval4316 x
  · exact rowEval4317 x
  · exact rowEval4318 x
  · exact rowEval4319 x
  · exact rowEval4320 x
  · exact rowEval4321 x
  · exact rowEval3557 x
  · exact rowEval3558 x
  · exact rowEval3559 x
  · exact rowEval4322 x
  · exact rowEval4323 x
  · exact rowEval4324 x
  · exact rowEval4325 x
  · exact rowEval4326 x
  · exact rowEval4327 x

theorem entryEval18_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_6 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck18_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_6]

def rows18_7 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2308, row2309, row2310, row2311, row2312, row2313, row3563, row3564, row3565, row2320, row2321, row2322, row2323, row2324, row2325, row4328, row4329, row4330, row4331, row4332, row4333, row3569, row3570, row3571, row4334, row4335, row4336, row4337, row4338, row4339]

theorem entryCheck18_7 : entry18_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_7 k)) := by decide +kernel

theorem rowsSound18_7 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2308 x
  · exact rowEval2309 x
  · exact rowEval2310 x
  · exact rowEval2311 x
  · exact rowEval2312 x
  · exact rowEval2313 x
  · exact rowEval3563 x
  · exact rowEval3564 x
  · exact rowEval3565 x
  · exact rowEval2320 x
  · exact rowEval2321 x
  · exact rowEval2322 x
  · exact rowEval2323 x
  · exact rowEval2324 x
  · exact rowEval2325 x
  · exact rowEval4328 x
  · exact rowEval4329 x
  · exact rowEval4330 x
  · exact rowEval4331 x
  · exact rowEval4332 x
  · exact rowEval4333 x
  · exact rowEval3569 x
  · exact rowEval3570 x
  · exact rowEval3571 x
  · exact rowEval4334 x
  · exact rowEval4335 x
  · exact rowEval4336 x
  · exact rowEval4337 x
  · exact rowEval4338 x
  · exact rowEval4339 x

theorem entryEval18_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_7 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck18_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_7]

def rows18_8 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2338, row2339, row2340, row2341, row2342, row2343, row3575, row3576, row3577, row2350, row2351, row2352, row2353, row2354, row2355, row4340, row4341, row4342, row4343, row4344, row4345, row3581, row3582, row3583, row4346, row4347, row4348, row4349, row4350, row4351]

theorem entryCheck18_8 : entry18_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_8 k)) := by decide +kernel

theorem rowsSound18_8 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2338 x
  · exact rowEval2339 x
  · exact rowEval2340 x
  · exact rowEval2341 x
  · exact rowEval2342 x
  · exact rowEval2343 x
  · exact rowEval3575 x
  · exact rowEval3576 x
  · exact rowEval3577 x
  · exact rowEval2350 x
  · exact rowEval2351 x
  · exact rowEval2352 x
  · exact rowEval2353 x
  · exact rowEval2354 x
  · exact rowEval2355 x
  · exact rowEval4340 x
  · exact rowEval4341 x
  · exact rowEval4342 x
  · exact rowEval4343 x
  · exact rowEval4344 x
  · exact rowEval4345 x
  · exact rowEval3581 x
  · exact rowEval3582 x
  · exact rowEval3583 x
  · exact rowEval4346 x
  · exact rowEval4347 x
  · exact rowEval4348 x
  · exact rowEval4349 x
  · exact rowEval4350 x
  · exact rowEval4351 x

theorem entryEval18_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_8 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck18_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_8]

def rows18_9 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2368, row2369, row2370, row2371, row2372, row2373, row3587, row3588, row3589, row2380, row2381, row2382, row2383, row2384, row2385, row4352, row4353, row4354, row4355, row4356, row4357, row3593, row3594, row3595, row4358, row4359, row4360, row4361, row4362, row4363]

theorem entryCheck18_9 : entry18_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_9 k)) := by decide +kernel

theorem rowsSound18_9 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2368 x
  · exact rowEval2369 x
  · exact rowEval2370 x
  · exact rowEval2371 x
  · exact rowEval2372 x
  · exact rowEval2373 x
  · exact rowEval3587 x
  · exact rowEval3588 x
  · exact rowEval3589 x
  · exact rowEval2380 x
  · exact rowEval2381 x
  · exact rowEval2382 x
  · exact rowEval2383 x
  · exact rowEval2384 x
  · exact rowEval2385 x
  · exact rowEval4352 x
  · exact rowEval4353 x
  · exact rowEval4354 x
  · exact rowEval4355 x
  · exact rowEval4356 x
  · exact rowEval4357 x
  · exact rowEval3593 x
  · exact rowEval3594 x
  · exact rowEval3595 x
  · exact rowEval4358 x
  · exact rowEval4359 x
  · exact rowEval4360 x
  · exact rowEval4361 x
  · exact rowEval4362 x
  · exact rowEval4363 x

theorem entryEval18_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_9 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck18_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_9]

def rows18_10 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2398, row2399, row2400, row2401, row2402, row2403, row3599, row3600, row3601, row2410, row2411, row2412, row2413, row2414, row2415, row4364, row4365, row4366, row4367, row4368, row4369, row3605, row3606, row3607, row4370, row4371, row4372, row4373, row4374, row4375]

theorem entryCheck18_10 : entry18_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_10 k)) := by decide +kernel

theorem rowsSound18_10 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2398 x
  · exact rowEval2399 x
  · exact rowEval2400 x
  · exact rowEval2401 x
  · exact rowEval2402 x
  · exact rowEval2403 x
  · exact rowEval3599 x
  · exact rowEval3600 x
  · exact rowEval3601 x
  · exact rowEval2410 x
  · exact rowEval2411 x
  · exact rowEval2412 x
  · exact rowEval2413 x
  · exact rowEval2414 x
  · exact rowEval2415 x
  · exact rowEval4364 x
  · exact rowEval4365 x
  · exact rowEval4366 x
  · exact rowEval4367 x
  · exact rowEval4368 x
  · exact rowEval4369 x
  · exact rowEval3605 x
  · exact rowEval3606 x
  · exact rowEval3607 x
  · exact rowEval4370 x
  · exact rowEval4371 x
  · exact rowEval4372 x
  · exact rowEval4373 x
  · exact rowEval4374 x
  · exact rowEval4375 x

theorem entryEval18_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_10 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck18_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_10]

def rows18_11 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2428, row2429, row2430, row2431, row2432, row2433, row3611, row3612, row3613, row2440, row2441, row2442, row2443, row2444, row2445, row4376, row4377, row4378, row4379, row4380, row4381, row3617, row3618, row3619, row4382, row4383, row4384, row4385, row4386, row4387]

theorem entryCheck18_11 : entry18_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_11 k)) := by decide +kernel

theorem rowsSound18_11 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2428 x
  · exact rowEval2429 x
  · exact rowEval2430 x
  · exact rowEval2431 x
  · exact rowEval2432 x
  · exact rowEval2433 x
  · exact rowEval3611 x
  · exact rowEval3612 x
  · exact rowEval3613 x
  · exact rowEval2440 x
  · exact rowEval2441 x
  · exact rowEval2442 x
  · exact rowEval2443 x
  · exact rowEval2444 x
  · exact rowEval2445 x
  · exact rowEval4376 x
  · exact rowEval4377 x
  · exact rowEval4378 x
  · exact rowEval4379 x
  · exact rowEval4380 x
  · exact rowEval4381 x
  · exact rowEval3617 x
  · exact rowEval3618 x
  · exact rowEval3619 x
  · exact rowEval4382 x
  · exact rowEval4383 x
  · exact rowEval4384 x
  · exact rowEval4385 x
  · exact rowEval4386 x
  · exact rowEval4387 x

theorem entryEval18_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_11 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck18_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_11]

def rows18_12 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2458, row2459, row2460, row2461, row2462, row2463, row3623, row3624, row3625, row2470, row2471, row2472, row2473, row2474, row2475, row4388, row4389, row4390, row4391, row4392, row4393, row3629, row3630, row3631, row4394, row4395, row4396, row4397, row4398, row4399]

theorem entryCheck18_12 : entry18_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_12 k)) := by decide +kernel

theorem rowsSound18_12 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2458 x
  · exact rowEval2459 x
  · exact rowEval2460 x
  · exact rowEval2461 x
  · exact rowEval2462 x
  · exact rowEval2463 x
  · exact rowEval3623 x
  · exact rowEval3624 x
  · exact rowEval3625 x
  · exact rowEval2470 x
  · exact rowEval2471 x
  · exact rowEval2472 x
  · exact rowEval2473 x
  · exact rowEval2474 x
  · exact rowEval2475 x
  · exact rowEval4388 x
  · exact rowEval4389 x
  · exact rowEval4390 x
  · exact rowEval4391 x
  · exact rowEval4392 x
  · exact rowEval4393 x
  · exact rowEval3629 x
  · exact rowEval3630 x
  · exact rowEval3631 x
  · exact rowEval4394 x
  · exact rowEval4395 x
  · exact rowEval4396 x
  · exact rowEval4397 x
  · exact rowEval4398 x
  · exact rowEval4399 x

theorem entryEval18_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_12 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck18_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_12]

def rows18_13 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4400, row4401, row4402, row4403, row4404, row4405, row3641, row3642, row3643, row4406, row4407, row4408, row4409, row4410, row4411, row4412, row4413, row4414, row4415, row4416, row4417, row3647, row3648, row3649, row4418, row4419, row4420, row4421, row4422, row4423]

theorem entryCheck18_13 : entry18_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_13 k)) := by decide +kernel

theorem rowsSound18_13 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval4400 x
  · exact rowEval4401 x
  · exact rowEval4402 x
  · exact rowEval4403 x
  · exact rowEval4404 x
  · exact rowEval4405 x
  · exact rowEval3641 x
  · exact rowEval3642 x
  · exact rowEval3643 x
  · exact rowEval4406 x
  · exact rowEval4407 x
  · exact rowEval4408 x
  · exact rowEval4409 x
  · exact rowEval4410 x
  · exact rowEval4411 x
  · exact rowEval4412 x
  · exact rowEval4413 x
  · exact rowEval4414 x
  · exact rowEval4415 x
  · exact rowEval4416 x
  · exact rowEval4417 x
  · exact rowEval3647 x
  · exact rowEval3648 x
  · exact rowEval3649 x
  · exact rowEval4418 x
  · exact rowEval4419 x
  · exact rowEval4420 x
  · exact rowEval4421 x
  · exact rowEval4422 x
  · exact rowEval4423 x

theorem entryEval18_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_13 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck18_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_13]

def rows18_14 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4424, row4425, row4426, row4427, row4428, row4429, row3659, row3660, row3661, row4430, row4431, row4432, row4433, row4434, row4435, row4436, row4437, row4438, row4439, row4440, row4441, row3665, row3666, row3667, row4442, row4443, row4444, row4445, row4446, row4447]

theorem entryCheck18_14 : entry18_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_14 k)) := by decide +kernel

theorem rowsSound18_14 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval4424 x
  · exact rowEval4425 x
  · exact rowEval4426 x
  · exact rowEval4427 x
  · exact rowEval4428 x
  · exact rowEval4429 x
  · exact rowEval3659 x
  · exact rowEval3660 x
  · exact rowEval3661 x
  · exact rowEval4430 x
  · exact rowEval4431 x
  · exact rowEval4432 x
  · exact rowEval4433 x
  · exact rowEval4434 x
  · exact rowEval4435 x
  · exact rowEval4436 x
  · exact rowEval4437 x
  · exact rowEval4438 x
  · exact rowEval4439 x
  · exact rowEval4440 x
  · exact rowEval4441 x
  · exact rowEval3665 x
  · exact rowEval3666 x
  · exact rowEval3667 x
  · exact rowEval4442 x
  · exact rowEval4443 x
  · exact rowEval4444 x
  · exact rowEval4445 x
  · exact rowEval4446 x
  · exact rowEval4447 x

theorem entryEval18_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_14 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck18_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_14]

def rows18_15 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4448, row4449, row4450, row4451, row4452, row4453, row3677, row3678, row3679, row4454, row4455, row4456, row4457, row4458, row4459, row4460, row4461, row4462, row4463, row4464, row4465, row3683, row3684, row3685, row4466, row4467, row4468, row4469, row4470, row4471]

theorem entryCheck18_15 : entry18_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_15 k)) := by decide +kernel

theorem rowsSound18_15 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval4448 x
  · exact rowEval4449 x
  · exact rowEval4450 x
  · exact rowEval4451 x
  · exact rowEval4452 x
  · exact rowEval4453 x
  · exact rowEval3677 x
  · exact rowEval3678 x
  · exact rowEval3679 x
  · exact rowEval4454 x
  · exact rowEval4455 x
  · exact rowEval4456 x
  · exact rowEval4457 x
  · exact rowEval4458 x
  · exact rowEval4459 x
  · exact rowEval4460 x
  · exact rowEval4461 x
  · exact rowEval4462 x
  · exact rowEval4463 x
  · exact rowEval4464 x
  · exact rowEval4465 x
  · exact rowEval3683 x
  · exact rowEval3684 x
  · exact rowEval3685 x
  · exact rowEval4466 x
  · exact rowEval4467 x
  · exact rowEval4468 x
  · exact rowEval4469 x
  · exact rowEval4470 x
  · exact rowEval4471 x

theorem entryEval18_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_15 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck18_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_15]

def rows18_16 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4472, row4473, row4474, row4475, row4476, row4477, row3695, row3696, row3697, row4478, row4479, row4480, row4481, row4482, row4483, row4484, row4485, row4486, row4487, row4488, row4489, row3701, row3702, row3703, row4490, row4491, row4492, row4493, row4494, row4495]

theorem entryCheck18_16 : entry18_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_16 k)) := by decide +kernel

theorem rowsSound18_16 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval4472 x
  · exact rowEval4473 x
  · exact rowEval4474 x
  · exact rowEval4475 x
  · exact rowEval4476 x
  · exact rowEval4477 x
  · exact rowEval3695 x
  · exact rowEval3696 x
  · exact rowEval3697 x
  · exact rowEval4478 x
  · exact rowEval4479 x
  · exact rowEval4480 x
  · exact rowEval4481 x
  · exact rowEval4482 x
  · exact rowEval4483 x
  · exact rowEval4484 x
  · exact rowEval4485 x
  · exact rowEval4486 x
  · exact rowEval4487 x
  · exact rowEval4488 x
  · exact rowEval4489 x
  · exact rowEval3701 x
  · exact rowEval3702 x
  · exact rowEval3703 x
  · exact rowEval4490 x
  · exact rowEval4491 x
  · exact rowEval4492 x
  · exact rowEval4493 x
  · exact rowEval4494 x
  · exact rowEval4495 x

theorem entryEval18_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_16 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck18_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_16]

def rows18_17 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4496, row4497, row4498, row4499, row4500, row4501, row4502, row4503, row4504, row4505, row4506, row4507, row4508, row4509, row4510, row4511, row4512, row4513, row4514, row4515, row4516, row4517, row4518, row4519, row4520, row4521, row4522, row4523, row4524, row4525]

theorem entryCheck18_17 : entry18_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_17 k)) := by decide +kernel

theorem rowsSound18_17 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form17) x := by
  fin_cases k
  · exact rowEval4496 x
  · exact rowEval4497 x
  · exact rowEval4498 x
  · exact rowEval4499 x
  · exact rowEval4500 x
  · exact rowEval4501 x
  · exact rowEval4502 x
  · exact rowEval4503 x
  · exact rowEval4504 x
  · exact rowEval4505 x
  · exact rowEval4506 x
  · exact rowEval4507 x
  · exact rowEval4508 x
  · exact rowEval4509 x
  · exact rowEval4510 x
  · exact rowEval4511 x
  · exact rowEval4512 x
  · exact rowEval4513 x
  · exact rowEval4514 x
  · exact rowEval4515 x
  · exact rowEval4516 x
  · exact rowEval4517 x
  · exact rowEval4518 x
  · exact rowEval4519 x
  · exact rowEval4520 x
  · exact rowEval4521 x
  · exact rowEval4522 x
  · exact rowEval4523 x
  · exact rowEval4524 x
  · exact rowEval4525 x

theorem entryEval18_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_17 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form17 B := by
  rw [entryCheck18_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_17]

def rows18_18 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4526, row4527, row4528, row4529, row4530, row4531, row4532, row4533, row4534, row4535, row4536, row4537, row4538, row4539, row4540, row4541, row4542, row4543, row4544, row4545, row4546, row4547, row4548, row4549, row4550, row4551, row4552, row4553, row4554, row4555]

theorem entryCheck18_18 : entry18_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form18.terms k).coefficient) (rows18_18 k)) := by decide +kernel

theorem rowsSound18_18 (k : Fin GramFunctions.Block1.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form18.terms k).tag (GramFunctions.Block1.form18.terms k).charge GramFunctions.Block1.form18) x := by
  fin_cases k
  · exact rowEval4526 x
  · exact rowEval4527 x
  · exact rowEval4528 x
  · exact rowEval4529 x
  · exact rowEval4530 x
  · exact rowEval4531 x
  · exact rowEval4532 x
  · exact rowEval4533 x
  · exact rowEval4534 x
  · exact rowEval4535 x
  · exact rowEval4536 x
  · exact rowEval4537 x
  · exact rowEval4538 x
  · exact rowEval4539 x
  · exact rowEval4540 x
  · exact rowEval4541 x
  · exact rowEval4542 x
  · exact rowEval4543 x
  · exact rowEval4544 x
  · exact rowEval4545 x
  · exact rowEval4546 x
  · exact rowEval4547 x
  · exact rowEval4548 x
  · exact rowEval4549 x
  · exact rowEval4550 x
  · exact rowEval4551 x
  · exact rowEval4552 x
  · exact rowEval4553 x
  · exact rowEval4554 x
  · exact rowEval4555 x

theorem entryEval18_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_18 (GramNormalization.eval B) = GramFunctions.Block1.form18.mixedGram GramFunctions.Block1.form18 B := by
  rw [entryCheck18_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form18 GramFunctions.Block1.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_18]

end MUB6.Certificate.GramEntries.Block1

end OAI
