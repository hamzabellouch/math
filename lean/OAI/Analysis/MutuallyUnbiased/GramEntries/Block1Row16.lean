import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block40
import OAI.Analysis.MutuallyUnbiased.GramRows.Block41
import OAI.Analysis.MutuallyUnbiased.GramRows.Block42
import OAI.Analysis.MutuallyUnbiased.GramRows.Block43
import OAI.Analysis.MutuallyUnbiased.GramRows.Block51
import OAI.Analysis.MutuallyUnbiased.GramRows.Block52

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2086, row2087, row2088, row3476, row3477, row3478, row2095, row2096, row2097, row3479, row3480, row3481, row3482, row3483, row3484, row3485, row3486, row3487]

theorem entryCheck16_0 : entry16_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_0 k)) := by decide +kernel

theorem rowsSound16_0 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval2086 x
  · exact rowEval2087 x
  · exact rowEval2088 x
  · exact rowEval3476 x
  · exact rowEval3477 x
  · exact rowEval3478 x
  · exact rowEval2095 x
  · exact rowEval2096 x
  · exact rowEval2097 x
  · exact rowEval3479 x
  · exact rowEval3480 x
  · exact rowEval3481 x
  · exact rowEval3482 x
  · exact rowEval3483 x
  · exact rowEval3484 x
  · exact rowEval3485 x
  · exact rowEval3486 x
  · exact rowEval3487 x

theorem entryEval16_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_0 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck16_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_0]

def rows16_1 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2116, row2117, row2118, row3488, row3489, row3490, row2125, row2126, row2127, row3491, row3492, row3493, row3494, row3495, row3496, row3497, row3498, row3499]

theorem entryCheck16_1 : entry16_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_1 k)) := by decide +kernel

theorem rowsSound16_1 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2116 x
  · exact rowEval2117 x
  · exact rowEval2118 x
  · exact rowEval3488 x
  · exact rowEval3489 x
  · exact rowEval3490 x
  · exact rowEval2125 x
  · exact rowEval2126 x
  · exact rowEval2127 x
  · exact rowEval3491 x
  · exact rowEval3492 x
  · exact rowEval3493 x
  · exact rowEval3494 x
  · exact rowEval3495 x
  · exact rowEval3496 x
  · exact rowEval3497 x
  · exact rowEval3498 x
  · exact rowEval3499 x

theorem entryEval16_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_1 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck16_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_1]

def rows16_2 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2146, row2147, row2148, row3500, row3501, row3502, row2155, row2156, row2157, row3503, row3504, row3505, row3506, row3507, row3508, row3509, row3510, row3511]

theorem entryCheck16_2 : entry16_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_2 k)) := by decide +kernel

theorem rowsSound16_2 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval2146 x
  · exact rowEval2147 x
  · exact rowEval2148 x
  · exact rowEval3500 x
  · exact rowEval3501 x
  · exact rowEval3502 x
  · exact rowEval2155 x
  · exact rowEval2156 x
  · exact rowEval2157 x
  · exact rowEval3503 x
  · exact rowEval3504 x
  · exact rowEval3505 x
  · exact rowEval3506 x
  · exact rowEval3507 x
  · exact rowEval3508 x
  · exact rowEval3509 x
  · exact rowEval3510 x
  · exact rowEval3511 x

theorem entryEval16_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_2 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck16_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_2]

def rows16_3 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2176, row2177, row2178, row3512, row3513, row3514, row2185, row2186, row2187, row3515, row3516, row3517, row3518, row3519, row3520, row3521, row3522, row3523]

theorem entryCheck16_3 : entry16_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_3 k)) := by decide +kernel

theorem rowsSound16_3 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2176 x
  · exact rowEval2177 x
  · exact rowEval2178 x
  · exact rowEval3512 x
  · exact rowEval3513 x
  · exact rowEval3514 x
  · exact rowEval2185 x
  · exact rowEval2186 x
  · exact rowEval2187 x
  · exact rowEval3515 x
  · exact rowEval3516 x
  · exact rowEval3517 x
  · exact rowEval3518 x
  · exact rowEval3519 x
  · exact rowEval3520 x
  · exact rowEval3521 x
  · exact rowEval3522 x
  · exact rowEval3523 x

theorem entryEval16_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_3 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck16_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_3]

def rows16_4 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2206, row2207, row2208, row3524, row3525, row3526, row2215, row2216, row2217, row3527, row3528, row3529, row3530, row3531, row3532, row3533, row3534, row3535]

theorem entryCheck16_4 : entry16_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_4 k)) := by decide +kernel

theorem rowsSound16_4 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2206 x
  · exact rowEval2207 x
  · exact rowEval2208 x
  · exact rowEval3524 x
  · exact rowEval3525 x
  · exact rowEval3526 x
  · exact rowEval2215 x
  · exact rowEval2216 x
  · exact rowEval2217 x
  · exact rowEval3527 x
  · exact rowEval3528 x
  · exact rowEval3529 x
  · exact rowEval3530 x
  · exact rowEval3531 x
  · exact rowEval3532 x
  · exact rowEval3533 x
  · exact rowEval3534 x
  · exact rowEval3535 x

theorem entryEval16_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_4 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck16_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_4]

def rows16_5 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2236, row2237, row2238, row3536, row3537, row3538, row2245, row2246, row2247, row3539, row3540, row3541, row3542, row3543, row3544, row3545, row3546, row3547]

theorem entryCheck16_5 : entry16_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_5 k)) := by decide +kernel

theorem rowsSound16_5 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2236 x
  · exact rowEval2237 x
  · exact rowEval2238 x
  · exact rowEval3536 x
  · exact rowEval3537 x
  · exact rowEval3538 x
  · exact rowEval2245 x
  · exact rowEval2246 x
  · exact rowEval2247 x
  · exact rowEval3539 x
  · exact rowEval3540 x
  · exact rowEval3541 x
  · exact rowEval3542 x
  · exact rowEval3543 x
  · exact rowEval3544 x
  · exact rowEval3545 x
  · exact rowEval3546 x
  · exact rowEval3547 x

theorem entryEval16_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_5 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck16_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_5]

def rows16_6 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2266, row2267, row2268, row3548, row3549, row3550, row2275, row2276, row2277, row3551, row3552, row3553, row3554, row3555, row3556, row3557, row3558, row3559]

theorem entryCheck16_6 : entry16_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_6 k)) := by decide +kernel

theorem rowsSound16_6 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2266 x
  · exact rowEval2267 x
  · exact rowEval2268 x
  · exact rowEval3548 x
  · exact rowEval3549 x
  · exact rowEval3550 x
  · exact rowEval2275 x
  · exact rowEval2276 x
  · exact rowEval2277 x
  · exact rowEval3551 x
  · exact rowEval3552 x
  · exact rowEval3553 x
  · exact rowEval3554 x
  · exact rowEval3555 x
  · exact rowEval3556 x
  · exact rowEval3557 x
  · exact rowEval3558 x
  · exact rowEval3559 x

theorem entryEval16_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_6 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck16_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_6]

def rows16_7 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2296, row2297, row2298, row3560, row3561, row3562, row2305, row2306, row2307, row3563, row3564, row3565, row3566, row3567, row3568, row3569, row3570, row3571]

theorem entryCheck16_7 : entry16_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_7 k)) := by decide +kernel

theorem rowsSound16_7 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2296 x
  · exact rowEval2297 x
  · exact rowEval2298 x
  · exact rowEval3560 x
  · exact rowEval3561 x
  · exact rowEval3562 x
  · exact rowEval2305 x
  · exact rowEval2306 x
  · exact rowEval2307 x
  · exact rowEval3563 x
  · exact rowEval3564 x
  · exact rowEval3565 x
  · exact rowEval3566 x
  · exact rowEval3567 x
  · exact rowEval3568 x
  · exact rowEval3569 x
  · exact rowEval3570 x
  · exact rowEval3571 x

theorem entryEval16_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_7 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck16_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_7]

def rows16_8 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2326, row2327, row2328, row3572, row3573, row3574, row2335, row2336, row2337, row3575, row3576, row3577, row3578, row3579, row3580, row3581, row3582, row3583]

theorem entryCheck16_8 : entry16_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_8 k)) := by decide +kernel

theorem rowsSound16_8 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2326 x
  · exact rowEval2327 x
  · exact rowEval2328 x
  · exact rowEval3572 x
  · exact rowEval3573 x
  · exact rowEval3574 x
  · exact rowEval2335 x
  · exact rowEval2336 x
  · exact rowEval2337 x
  · exact rowEval3575 x
  · exact rowEval3576 x
  · exact rowEval3577 x
  · exact rowEval3578 x
  · exact rowEval3579 x
  · exact rowEval3580 x
  · exact rowEval3581 x
  · exact rowEval3582 x
  · exact rowEval3583 x

theorem entryEval16_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_8 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck16_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_8]

def rows16_9 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2356, row2357, row2358, row3584, row3585, row3586, row2365, row2366, row2367, row3587, row3588, row3589, row3590, row3591, row3592, row3593, row3594, row3595]

theorem entryCheck16_9 : entry16_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_9 k)) := by decide +kernel

theorem rowsSound16_9 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2356 x
  · exact rowEval2357 x
  · exact rowEval2358 x
  · exact rowEval3584 x
  · exact rowEval3585 x
  · exact rowEval3586 x
  · exact rowEval2365 x
  · exact rowEval2366 x
  · exact rowEval2367 x
  · exact rowEval3587 x
  · exact rowEval3588 x
  · exact rowEval3589 x
  · exact rowEval3590 x
  · exact rowEval3591 x
  · exact rowEval3592 x
  · exact rowEval3593 x
  · exact rowEval3594 x
  · exact rowEval3595 x

theorem entryEval16_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_9 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck16_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_9]

def rows16_10 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2386, row2387, row2388, row3596, row3597, row3598, row2395, row2396, row2397, row3599, row3600, row3601, row3602, row3603, row3604, row3605, row3606, row3607]

theorem entryCheck16_10 : entry16_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_10 k)) := by decide +kernel

theorem rowsSound16_10 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2386 x
  · exact rowEval2387 x
  · exact rowEval2388 x
  · exact rowEval3596 x
  · exact rowEval3597 x
  · exact rowEval3598 x
  · exact rowEval2395 x
  · exact rowEval2396 x
  · exact rowEval2397 x
  · exact rowEval3599 x
  · exact rowEval3600 x
  · exact rowEval3601 x
  · exact rowEval3602 x
  · exact rowEval3603 x
  · exact rowEval3604 x
  · exact rowEval3605 x
  · exact rowEval3606 x
  · exact rowEval3607 x

theorem entryEval16_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_10 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck16_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_10]

def rows16_11 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2416, row2417, row2418, row3608, row3609, row3610, row2425, row2426, row2427, row3611, row3612, row3613, row3614, row3615, row3616, row3617, row3618, row3619]

theorem entryCheck16_11 : entry16_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_11 k)) := by decide +kernel

theorem rowsSound16_11 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2416 x
  · exact rowEval2417 x
  · exact rowEval2418 x
  · exact rowEval3608 x
  · exact rowEval3609 x
  · exact rowEval3610 x
  · exact rowEval2425 x
  · exact rowEval2426 x
  · exact rowEval2427 x
  · exact rowEval3611 x
  · exact rowEval3612 x
  · exact rowEval3613 x
  · exact rowEval3614 x
  · exact rowEval3615 x
  · exact rowEval3616 x
  · exact rowEval3617 x
  · exact rowEval3618 x
  · exact rowEval3619 x

theorem entryEval16_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_11 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck16_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_11]

def rows16_12 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2446, row2447, row2448, row3620, row3621, row3622, row2455, row2456, row2457, row3623, row3624, row3625, row3626, row3627, row3628, row3629, row3630, row3631]

theorem entryCheck16_12 : entry16_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_12 k)) := by decide +kernel

theorem rowsSound16_12 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2446 x
  · exact rowEval2447 x
  · exact rowEval2448 x
  · exact rowEval3620 x
  · exact rowEval3621 x
  · exact rowEval3622 x
  · exact rowEval2455 x
  · exact rowEval2456 x
  · exact rowEval2457 x
  · exact rowEval3623 x
  · exact rowEval3624 x
  · exact rowEval3625 x
  · exact rowEval3626 x
  · exact rowEval3627 x
  · exact rowEval3628 x
  · exact rowEval3629 x
  · exact rowEval3630 x
  · exact rowEval3631 x

theorem entryEval16_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_12 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck16_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_12]

def rows16_13 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3632, row3633, row3634, row3635, row3636, row3637, row3638, row3639, row3640, row3641, row3642, row3643, row3644, row3645, row3646, row3647, row3648, row3649]

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval3632 x
  · exact rowEval3633 x
  · exact rowEval3634 x
  · exact rowEval3635 x
  · exact rowEval3636 x
  · exact rowEval3637 x
  · exact rowEval3638 x
  · exact rowEval3639 x
  · exact rowEval3640 x
  · exact rowEval3641 x
  · exact rowEval3642 x
  · exact rowEval3643 x
  · exact rowEval3644 x
  · exact rowEval3645 x
  · exact rowEval3646 x
  · exact rowEval3647 x
  · exact rowEval3648 x
  · exact rowEval3649 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

def rows16_14 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3650, row3651, row3652, row3653, row3654, row3655, row3656, row3657, row3658, row3659, row3660, row3661, row3662, row3663, row3664, row3665, row3666, row3667]

theorem entryCheck16_14 : entry16_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_14 k)) := by decide +kernel

theorem rowsSound16_14 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval3650 x
  · exact rowEval3651 x
  · exact rowEval3652 x
  · exact rowEval3653 x
  · exact rowEval3654 x
  · exact rowEval3655 x
  · exact rowEval3656 x
  · exact rowEval3657 x
  · exact rowEval3658 x
  · exact rowEval3659 x
  · exact rowEval3660 x
  · exact rowEval3661 x
  · exact rowEval3662 x
  · exact rowEval3663 x
  · exact rowEval3664 x
  · exact rowEval3665 x
  · exact rowEval3666 x
  · exact rowEval3667 x

theorem entryEval16_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_14 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck16_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_14]

def rows16_15 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3668, row3669, row3670, row3671, row3672, row3673, row3674, row3675, row3676, row3677, row3678, row3679, row3680, row3681, row3682, row3683, row3684, row3685]

theorem entryCheck16_15 : entry16_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_15 k)) := by decide +kernel

theorem rowsSound16_15 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval3668 x
  · exact rowEval3669 x
  · exact rowEval3670 x
  · exact rowEval3671 x
  · exact rowEval3672 x
  · exact rowEval3673 x
  · exact rowEval3674 x
  · exact rowEval3675 x
  · exact rowEval3676 x
  · exact rowEval3677 x
  · exact rowEval3678 x
  · exact rowEval3679 x
  · exact rowEval3680 x
  · exact rowEval3681 x
  · exact rowEval3682 x
  · exact rowEval3683 x
  · exact rowEval3684 x
  · exact rowEval3685 x

theorem entryEval16_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_15 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck16_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_15]

def rows16_16 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3686, row3687, row3688, row3689, row3690, row3691, row3692, row3693, row3694, row3695, row3696, row3697, row3698, row3699, row3700, row3701, row3702, row3703]

theorem entryCheck16_16 : entry16_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form16.terms k).coefficient) (rows16_16 k)) := by decide +kernel

theorem rowsSound16_16 (k : Fin GramFunctions.Block1.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form16.terms k).tag (GramFunctions.Block1.form16.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval3686 x
  · exact rowEval3687 x
  · exact rowEval3688 x
  · exact rowEval3689 x
  · exact rowEval3690 x
  · exact rowEval3691 x
  · exact rowEval3692 x
  · exact rowEval3693 x
  · exact rowEval3694 x
  · exact rowEval3695 x
  · exact rowEval3696 x
  · exact rowEval3697 x
  · exact rowEval3698 x
  · exact rowEval3699 x
  · exact rowEval3700 x
  · exact rowEval3701 x
  · exact rowEval3702 x
  · exact rowEval3703 x

theorem entryEval16_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_16 (GramNormalization.eval B) = GramFunctions.Block1.form16.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck16_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form16 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_16]

end MUB6.Certificate.GramEntries.Block1

end OAI
