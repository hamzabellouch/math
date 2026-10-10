import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block134
import OAI.Analysis.MutuallyUnbiased.GramRows.Block135
import OAI.Analysis.MutuallyUnbiased.GramRows.Block136
import OAI.Analysis.MutuallyUnbiased.GramRows.Block137
import OAI.Analysis.MutuallyUnbiased.GramRows.Block138

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14205, row14206, row14207, row14208, row14209, row14210, row14211, row14212, row14213, row14214, row14215, row14216, row14217, row14218, row14219, row14220, row14221, row14222, row14223, row14224, row14225, row14226, row14227, row14228, row14229, row14230, row14231, row14232, row14233, row14234, row14235, row14236, row14237, row14238, row14239, row14240]

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval14205 x
  · exact rowEval14206 x
  · exact rowEval14207 x
  · exact rowEval14208 x
  · exact rowEval14209 x
  · exact rowEval14210 x
  · exact rowEval14211 x
  · exact rowEval14212 x
  · exact rowEval14213 x
  · exact rowEval14214 x
  · exact rowEval14215 x
  · exact rowEval14216 x
  · exact rowEval14217 x
  · exact rowEval14218 x
  · exact rowEval14219 x
  · exact rowEval14220 x
  · exact rowEval14221 x
  · exact rowEval14222 x
  · exact rowEval14223 x
  · exact rowEval14224 x
  · exact rowEval14225 x
  · exact rowEval14226 x
  · exact rowEval14227 x
  · exact rowEval14228 x
  · exact rowEval14229 x
  · exact rowEval14230 x
  · exact rowEval14231 x
  · exact rowEval14232 x
  · exact rowEval14233 x
  · exact rowEval14234 x
  · exact rowEval14235 x
  · exact rowEval14236 x
  · exact rowEval14237 x
  · exact rowEval14238 x
  · exact rowEval14239 x
  · exact rowEval14240 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

def rows10_1 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14241, row14242, row14243, row14244, row14245, row14246, row14247, row14248, row14249, row14250, row14251, row14252, row14253, row14254, row14255, row14256, row14257, row14258, row14259, row14260, row14261, row14262, row14263, row14264, row14265, row14266, row14267, row14268, row14269, row14270, row14271, row14272, row14273, row14274, row14275, row14276]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval14241 x
  · exact rowEval14242 x
  · exact rowEval14243 x
  · exact rowEval14244 x
  · exact rowEval14245 x
  · exact rowEval14246 x
  · exact rowEval14247 x
  · exact rowEval14248 x
  · exact rowEval14249 x
  · exact rowEval14250 x
  · exact rowEval14251 x
  · exact rowEval14252 x
  · exact rowEval14253 x
  · exact rowEval14254 x
  · exact rowEval14255 x
  · exact rowEval14256 x
  · exact rowEval14257 x
  · exact rowEval14258 x
  · exact rowEval14259 x
  · exact rowEval14260 x
  · exact rowEval14261 x
  · exact rowEval14262 x
  · exact rowEval14263 x
  · exact rowEval14264 x
  · exact rowEval14265 x
  · exact rowEval14266 x
  · exact rowEval14267 x
  · exact rowEval14268 x
  · exact rowEval14269 x
  · exact rowEval14270 x
  · exact rowEval14271 x
  · exact rowEval14272 x
  · exact rowEval14273 x
  · exact rowEval14274 x
  · exact rowEval14275 x
  · exact rowEval14276 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

def rows10_2 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14277, row14278, row14279, row14280, row14281, row14282, row14283, row14284, row14285, row14286, row14287, row14288, row14289, row14290, row14291, row14292, row14293, row14294, row14295, row14296, row14297, row14298, row14299, row14300, row14301, row14302, row14303, row14304, row14305, row14306, row14307, row14308, row14309, row14310, row14311, row14312]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval14277 x
  · exact rowEval14278 x
  · exact rowEval14279 x
  · exact rowEval14280 x
  · exact rowEval14281 x
  · exact rowEval14282 x
  · exact rowEval14283 x
  · exact rowEval14284 x
  · exact rowEval14285 x
  · exact rowEval14286 x
  · exact rowEval14287 x
  · exact rowEval14288 x
  · exact rowEval14289 x
  · exact rowEval14290 x
  · exact rowEval14291 x
  · exact rowEval14292 x
  · exact rowEval14293 x
  · exact rowEval14294 x
  · exact rowEval14295 x
  · exact rowEval14296 x
  · exact rowEval14297 x
  · exact rowEval14298 x
  · exact rowEval14299 x
  · exact rowEval14300 x
  · exact rowEval14301 x
  · exact rowEval14302 x
  · exact rowEval14303 x
  · exact rowEval14304 x
  · exact rowEval14305 x
  · exact rowEval14306 x
  · exact rowEval14307 x
  · exact rowEval14308 x
  · exact rowEval14309 x
  · exact rowEval14310 x
  · exact rowEval14311 x
  · exact rowEval14312 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

def rows10_3 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14313, row14314, row14315, row14316, row14317, row14318, row14319, row14320, row14321, row14322, row14323, row14324, row14325, row14326, row14327, row14328, row14329, row14330, row14331, row14332, row14333, row14334, row14335, row14336, row14337, row14338, row14339, row14340, row14341, row14342, row14343, row14344, row14345, row14346, row14347, row14348]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval14313 x
  · exact rowEval14314 x
  · exact rowEval14315 x
  · exact rowEval14316 x
  · exact rowEval14317 x
  · exact rowEval14318 x
  · exact rowEval14319 x
  · exact rowEval14320 x
  · exact rowEval14321 x
  · exact rowEval14322 x
  · exact rowEval14323 x
  · exact rowEval14324 x
  · exact rowEval14325 x
  · exact rowEval14326 x
  · exact rowEval14327 x
  · exact rowEval14328 x
  · exact rowEval14329 x
  · exact rowEval14330 x
  · exact rowEval14331 x
  · exact rowEval14332 x
  · exact rowEval14333 x
  · exact rowEval14334 x
  · exact rowEval14335 x
  · exact rowEval14336 x
  · exact rowEval14337 x
  · exact rowEval14338 x
  · exact rowEval14339 x
  · exact rowEval14340 x
  · exact rowEval14341 x
  · exact rowEval14342 x
  · exact rowEval14343 x
  · exact rowEval14344 x
  · exact rowEval14345 x
  · exact rowEval14346 x
  · exact rowEval14347 x
  · exact rowEval14348 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

def rows10_4 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14349, row14350, row14351, row14352, row14353, row14354, row14355, row14356, row14357, row14358, row14359, row14360, row14361, row14362, row14363, row14364, row14365, row14366, row14367, row14368, row14369, row14370, row14371, row14372, row14373, row14374, row14375, row14376, row14377, row14378, row14379, row14380, row14381, row14382, row14383, row14384]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval14349 x
  · exact rowEval14350 x
  · exact rowEval14351 x
  · exact rowEval14352 x
  · exact rowEval14353 x
  · exact rowEval14354 x
  · exact rowEval14355 x
  · exact rowEval14356 x
  · exact rowEval14357 x
  · exact rowEval14358 x
  · exact rowEval14359 x
  · exact rowEval14360 x
  · exact rowEval14361 x
  · exact rowEval14362 x
  · exact rowEval14363 x
  · exact rowEval14364 x
  · exact rowEval14365 x
  · exact rowEval14366 x
  · exact rowEval14367 x
  · exact rowEval14368 x
  · exact rowEval14369 x
  · exact rowEval14370 x
  · exact rowEval14371 x
  · exact rowEval14372 x
  · exact rowEval14373 x
  · exact rowEval14374 x
  · exact rowEval14375 x
  · exact rowEval14376 x
  · exact rowEval14377 x
  · exact rowEval14378 x
  · exact rowEval14379 x
  · exact rowEval14380 x
  · exact rowEval14381 x
  · exact rowEval14382 x
  · exact rowEval14383 x
  · exact rowEval14384 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

def rows10_5 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14385, row14386, row14387, row14388, row14389, row14390, row14391, row14392, row14393, row14394, row14395, row14396, row14397, row14398, row14399, row14400, row14401, row14402, row14403, row14404, row14405, row14406, row14407, row14408, row14409, row14410, row14411, row14412, row14413, row14414, row14415, row14416, row14417, row14418, row14419, row14420]

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval14385 x
  · exact rowEval14386 x
  · exact rowEval14387 x
  · exact rowEval14388 x
  · exact rowEval14389 x
  · exact rowEval14390 x
  · exact rowEval14391 x
  · exact rowEval14392 x
  · exact rowEval14393 x
  · exact rowEval14394 x
  · exact rowEval14395 x
  · exact rowEval14396 x
  · exact rowEval14397 x
  · exact rowEval14398 x
  · exact rowEval14399 x
  · exact rowEval14400 x
  · exact rowEval14401 x
  · exact rowEval14402 x
  · exact rowEval14403 x
  · exact rowEval14404 x
  · exact rowEval14405 x
  · exact rowEval14406 x
  · exact rowEval14407 x
  · exact rowEval14408 x
  · exact rowEval14409 x
  · exact rowEval14410 x
  · exact rowEval14411 x
  · exact rowEval14412 x
  · exact rowEval14413 x
  · exact rowEval14414 x
  · exact rowEval14415 x
  · exact rowEval14416 x
  · exact rowEval14417 x
  · exact rowEval14418 x
  · exact rowEval14419 x
  · exact rowEval14420 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

def rows10_6 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14421, row14422, row14423, row14424, row14425, row14426, row14427, row14428, row14429, row14430, row14431, row14432, row14433, row14434, row14435, row14436, row14437, row14438, row14439, row14440, row14441, row14442, row14443, row14444, row14445, row14446, row14447, row14448, row14449, row14450, row14451, row14452, row14453, row14454, row14455, row14456]

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval14421 x
  · exact rowEval14422 x
  · exact rowEval14423 x
  · exact rowEval14424 x
  · exact rowEval14425 x
  · exact rowEval14426 x
  · exact rowEval14427 x
  · exact rowEval14428 x
  · exact rowEval14429 x
  · exact rowEval14430 x
  · exact rowEval14431 x
  · exact rowEval14432 x
  · exact rowEval14433 x
  · exact rowEval14434 x
  · exact rowEval14435 x
  · exact rowEval14436 x
  · exact rowEval14437 x
  · exact rowEval14438 x
  · exact rowEval14439 x
  · exact rowEval14440 x
  · exact rowEval14441 x
  · exact rowEval14442 x
  · exact rowEval14443 x
  · exact rowEval14444 x
  · exact rowEval14445 x
  · exact rowEval14446 x
  · exact rowEval14447 x
  · exact rowEval14448 x
  · exact rowEval14449 x
  · exact rowEval14450 x
  · exact rowEval14451 x
  · exact rowEval14452 x
  · exact rowEval14453 x
  · exact rowEval14454 x
  · exact rowEval14455 x
  · exact rowEval14456 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

def rows10_7 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14457, row14458, row14459, row14460, row14461, row14462, row14463, row14464, row14465, row14466, row14467, row14468, row14469, row14470, row14471, row14472, row14473, row14474, row14475, row14476, row14477, row14478, row14479, row14480, row14481, row14482, row14483, row14484, row14485, row14486, row14487, row14488, row14489, row14490, row14491, row14492]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval14457 x
  · exact rowEval14458 x
  · exact rowEval14459 x
  · exact rowEval14460 x
  · exact rowEval14461 x
  · exact rowEval14462 x
  · exact rowEval14463 x
  · exact rowEval14464 x
  · exact rowEval14465 x
  · exact rowEval14466 x
  · exact rowEval14467 x
  · exact rowEval14468 x
  · exact rowEval14469 x
  · exact rowEval14470 x
  · exact rowEval14471 x
  · exact rowEval14472 x
  · exact rowEval14473 x
  · exact rowEval14474 x
  · exact rowEval14475 x
  · exact rowEval14476 x
  · exact rowEval14477 x
  · exact rowEval14478 x
  · exact rowEval14479 x
  · exact rowEval14480 x
  · exact rowEval14481 x
  · exact rowEval14482 x
  · exact rowEval14483 x
  · exact rowEval14484 x
  · exact rowEval14485 x
  · exact rowEval14486 x
  · exact rowEval14487 x
  · exact rowEval14488 x
  · exact rowEval14489 x
  · exact rowEval14490 x
  · exact rowEval14491 x
  · exact rowEval14492 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

def rows10_8 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14493, row14494, row14495, row14496, row14497, row14498, row14499, row14500, row14501, row14502, row14503, row14504, row14505, row14506, row14507, row14508, row14509, row14510, row14511, row14512, row14513, row14514, row14515, row14516, row14517, row14518, row14519, row14520, row14521, row14522, row14523, row14524, row14525, row14526, row14527, row14528]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval14493 x
  · exact rowEval14494 x
  · exact rowEval14495 x
  · exact rowEval14496 x
  · exact rowEval14497 x
  · exact rowEval14498 x
  · exact rowEval14499 x
  · exact rowEval14500 x
  · exact rowEval14501 x
  · exact rowEval14502 x
  · exact rowEval14503 x
  · exact rowEval14504 x
  · exact rowEval14505 x
  · exact rowEval14506 x
  · exact rowEval14507 x
  · exact rowEval14508 x
  · exact rowEval14509 x
  · exact rowEval14510 x
  · exact rowEval14511 x
  · exact rowEval14512 x
  · exact rowEval14513 x
  · exact rowEval14514 x
  · exact rowEval14515 x
  · exact rowEval14516 x
  · exact rowEval14517 x
  · exact rowEval14518 x
  · exact rowEval14519 x
  · exact rowEval14520 x
  · exact rowEval14521 x
  · exact rowEval14522 x
  · exact rowEval14523 x
  · exact rowEval14524 x
  · exact rowEval14525 x
  · exact rowEval14526 x
  · exact rowEval14527 x
  · exact rowEval14528 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

def rows10_9 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14529, row14530, row14531, row14532, row14533, row14534, row14535, row14536, row14537, row14538, row14539, row14540, row14541, row14542, row14543, row14544, row14545, row14546, row14547, row14548, row14549, row14550, row14551, row14552, row14553, row14554, row14555, row14556, row14557, row14558, row14559, row14560, row14561, row14562, row14563, row14564]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval14529 x
  · exact rowEval14530 x
  · exact rowEval14531 x
  · exact rowEval14532 x
  · exact rowEval14533 x
  · exact rowEval14534 x
  · exact rowEval14535 x
  · exact rowEval14536 x
  · exact rowEval14537 x
  · exact rowEval14538 x
  · exact rowEval14539 x
  · exact rowEval14540 x
  · exact rowEval14541 x
  · exact rowEval14542 x
  · exact rowEval14543 x
  · exact rowEval14544 x
  · exact rowEval14545 x
  · exact rowEval14546 x
  · exact rowEval14547 x
  · exact rowEval14548 x
  · exact rowEval14549 x
  · exact rowEval14550 x
  · exact rowEval14551 x
  · exact rowEval14552 x
  · exact rowEval14553 x
  · exact rowEval14554 x
  · exact rowEval14555 x
  · exact rowEval14556 x
  · exact rowEval14557 x
  · exact rowEval14558 x
  · exact rowEval14559 x
  · exact rowEval14560 x
  · exact rowEval14561 x
  · exact rowEval14562 x
  · exact rowEval14563 x
  · exact rowEval14564 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

def rows10_10 : Fin GramFunctions.Block4.form10.size → Integer.Sparse Key := ![row14565, row14566, row14567, row14568, row14569, row14570, row14571, row14572, row14573, row14574, row14575, row14576, row14577, row14578, row14579, row14580, row14581, row14582, row14583, row14584, row14585, row14586, row14587, row14588, row14589, row14590, row14591, row14592, row14593, row14594, row14595, row14596, row14597, row14598, row14599, row14600]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block4.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form10.terms k).tag (GramFunctions.Block4.form10.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval14565 x
  · exact rowEval14566 x
  · exact rowEval14567 x
  · exact rowEval14568 x
  · exact rowEval14569 x
  · exact rowEval14570 x
  · exact rowEval14571 x
  · exact rowEval14572 x
  · exact rowEval14573 x
  · exact rowEval14574 x
  · exact rowEval14575 x
  · exact rowEval14576 x
  · exact rowEval14577 x
  · exact rowEval14578 x
  · exact rowEval14579 x
  · exact rowEval14580 x
  · exact rowEval14581 x
  · exact rowEval14582 x
  · exact rowEval14583 x
  · exact rowEval14584 x
  · exact rowEval14585 x
  · exact rowEval14586 x
  · exact rowEval14587 x
  · exact rowEval14588 x
  · exact rowEval14589 x
  · exact rowEval14590 x
  · exact rowEval14591 x
  · exact rowEval14592 x
  · exact rowEval14593 x
  · exact rowEval14594 x
  · exact rowEval14595 x
  · exact rowEval14596 x
  · exact rowEval14597 x
  · exact rowEval14598 x
  · exact rowEval14599 x
  · exact rowEval14600 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block4.form10.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form10 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block4

end OAI
