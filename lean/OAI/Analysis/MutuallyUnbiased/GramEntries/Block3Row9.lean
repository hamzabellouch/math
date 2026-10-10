import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block83
import OAI.Analysis.MutuallyUnbiased.GramRows.Block84
import OAI.Analysis.MutuallyUnbiased.GramRows.Block88
import OAI.Analysis.MutuallyUnbiased.GramRows.Block89
import OAI.Analysis.MutuallyUnbiased.GramRows.Block90

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7586, row7587, row7588, row7589, row7590, row7591, row7592, row7593, row7594, row7595, row7596, row7597, row7598, row7599, row7600, row7601, row7602, row7603, row7604, row7605, row7606, row7607, row7608, row7609, row8269, row8270, row8271, row8272, row8273, row8274, row8275, row8276, row8277, row8278, row8279, row8280]

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7586 x
  · exact rowEval7587 x
  · exact rowEval7588 x
  · exact rowEval7589 x
  · exact rowEval7590 x
  · exact rowEval7591 x
  · exact rowEval7592 x
  · exact rowEval7593 x
  · exact rowEval7594 x
  · exact rowEval7595 x
  · exact rowEval7596 x
  · exact rowEval7597 x
  · exact rowEval7598 x
  · exact rowEval7599 x
  · exact rowEval7600 x
  · exact rowEval7601 x
  · exact rowEval7602 x
  · exact rowEval7603 x
  · exact rowEval7604 x
  · exact rowEval7605 x
  · exact rowEval7606 x
  · exact rowEval7607 x
  · exact rowEval7608 x
  · exact rowEval7609 x
  · exact rowEval8269 x
  · exact rowEval8270 x
  · exact rowEval8271 x
  · exact rowEval8272 x
  · exact rowEval8273 x
  · exact rowEval8274 x
  · exact rowEval8275 x
  · exact rowEval8276 x
  · exact rowEval8277 x
  · exact rowEval8278 x
  · exact rowEval8279 x
  · exact rowEval8280 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

def rows9_1 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7622, row7623, row7624, row7625, row7626, row7627, row7628, row7629, row7630, row7631, row7632, row7633, row7634, row7635, row7636, row7637, row7638, row7639, row7640, row7641, row7642, row7643, row7644, row7645, row8281, row8282, row8283, row8284, row8285, row8286, row8287, row8288, row8289, row8290, row8291, row8292]

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7622 x
  · exact rowEval7623 x
  · exact rowEval7624 x
  · exact rowEval7625 x
  · exact rowEval7626 x
  · exact rowEval7627 x
  · exact rowEval7628 x
  · exact rowEval7629 x
  · exact rowEval7630 x
  · exact rowEval7631 x
  · exact rowEval7632 x
  · exact rowEval7633 x
  · exact rowEval7634 x
  · exact rowEval7635 x
  · exact rowEval7636 x
  · exact rowEval7637 x
  · exact rowEval7638 x
  · exact rowEval7639 x
  · exact rowEval7640 x
  · exact rowEval7641 x
  · exact rowEval7642 x
  · exact rowEval7643 x
  · exact rowEval7644 x
  · exact rowEval7645 x
  · exact rowEval8281 x
  · exact rowEval8282 x
  · exact rowEval8283 x
  · exact rowEval8284 x
  · exact rowEval8285 x
  · exact rowEval8286 x
  · exact rowEval8287 x
  · exact rowEval8288 x
  · exact rowEval8289 x
  · exact rowEval8290 x
  · exact rowEval8291 x
  · exact rowEval8292 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

def rows9_2 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7658, row7659, row7660, row7661, row7662, row7663, row7664, row7665, row7666, row7667, row7668, row7669, row7670, row7671, row7672, row7673, row7674, row7675, row7676, row7677, row7678, row7679, row7680, row7681, row8293, row8294, row8295, row8296, row8297, row8298, row8299, row8300, row8301, row8302, row8303, row8304]

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7658 x
  · exact rowEval7659 x
  · exact rowEval7660 x
  · exact rowEval7661 x
  · exact rowEval7662 x
  · exact rowEval7663 x
  · exact rowEval7664 x
  · exact rowEval7665 x
  · exact rowEval7666 x
  · exact rowEval7667 x
  · exact rowEval7668 x
  · exact rowEval7669 x
  · exact rowEval7670 x
  · exact rowEval7671 x
  · exact rowEval7672 x
  · exact rowEval7673 x
  · exact rowEval7674 x
  · exact rowEval7675 x
  · exact rowEval7676 x
  · exact rowEval7677 x
  · exact rowEval7678 x
  · exact rowEval7679 x
  · exact rowEval7680 x
  · exact rowEval7681 x
  · exact rowEval8293 x
  · exact rowEval8294 x
  · exact rowEval8295 x
  · exact rowEval8296 x
  · exact rowEval8297 x
  · exact rowEval8298 x
  · exact rowEval8299 x
  · exact rowEval8300 x
  · exact rowEval8301 x
  · exact rowEval8302 x
  · exact rowEval8303 x
  · exact rowEval8304 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

def rows9_3 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7694, row7695, row7696, row7697, row7698, row7699, row7700, row7701, row7702, row7703, row7704, row7705, row7706, row7707, row7708, row7709, row7710, row7711, row7712, row7713, row7714, row7715, row7716, row7717, row8305, row8306, row8307, row8308, row8309, row8310, row8311, row8312, row8313, row8314, row8315, row8316]

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7694 x
  · exact rowEval7695 x
  · exact rowEval7696 x
  · exact rowEval7697 x
  · exact rowEval7698 x
  · exact rowEval7699 x
  · exact rowEval7700 x
  · exact rowEval7701 x
  · exact rowEval7702 x
  · exact rowEval7703 x
  · exact rowEval7704 x
  · exact rowEval7705 x
  · exact rowEval7706 x
  · exact rowEval7707 x
  · exact rowEval7708 x
  · exact rowEval7709 x
  · exact rowEval7710 x
  · exact rowEval7711 x
  · exact rowEval7712 x
  · exact rowEval7713 x
  · exact rowEval7714 x
  · exact rowEval7715 x
  · exact rowEval7716 x
  · exact rowEval7717 x
  · exact rowEval8305 x
  · exact rowEval8306 x
  · exact rowEval8307 x
  · exact rowEval8308 x
  · exact rowEval8309 x
  · exact rowEval8310 x
  · exact rowEval8311 x
  · exact rowEval8312 x
  · exact rowEval8313 x
  · exact rowEval8314 x
  · exact rowEval8315 x
  · exact rowEval8316 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

def rows9_4 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7730, row7731, row7732, row7733, row7734, row7735, row7736, row7737, row7738, row7739, row7740, row7741, row7742, row7743, row7744, row7745, row7746, row7747, row7748, row7749, row7750, row7751, row7752, row7753, row8317, row8318, row8319, row8320, row8321, row8322, row8323, row8324, row8325, row8326, row8327, row8328]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7730 x
  · exact rowEval7731 x
  · exact rowEval7732 x
  · exact rowEval7733 x
  · exact rowEval7734 x
  · exact rowEval7735 x
  · exact rowEval7736 x
  · exact rowEval7737 x
  · exact rowEval7738 x
  · exact rowEval7739 x
  · exact rowEval7740 x
  · exact rowEval7741 x
  · exact rowEval7742 x
  · exact rowEval7743 x
  · exact rowEval7744 x
  · exact rowEval7745 x
  · exact rowEval7746 x
  · exact rowEval7747 x
  · exact rowEval7748 x
  · exact rowEval7749 x
  · exact rowEval7750 x
  · exact rowEval7751 x
  · exact rowEval7752 x
  · exact rowEval7753 x
  · exact rowEval8317 x
  · exact rowEval8318 x
  · exact rowEval8319 x
  · exact rowEval8320 x
  · exact rowEval8321 x
  · exact rowEval8322 x
  · exact rowEval8323 x
  · exact rowEval8324 x
  · exact rowEval8325 x
  · exact rowEval8326 x
  · exact rowEval8327 x
  · exact rowEval8328 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

def rows9_5 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7766, row7767, row7768, row7769, row7770, row7771, row7772, row7773, row7774, row7775, row7776, row7777, row7778, row7779, row7780, row7781, row7782, row7783, row7784, row7785, row7786, row7787, row7788, row7789, row8329, row8330, row8331, row8332, row8333, row8334, row8335, row8336, row8337, row8338, row8339, row8340]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval7766 x
  · exact rowEval7767 x
  · exact rowEval7768 x
  · exact rowEval7769 x
  · exact rowEval7770 x
  · exact rowEval7771 x
  · exact rowEval7772 x
  · exact rowEval7773 x
  · exact rowEval7774 x
  · exact rowEval7775 x
  · exact rowEval7776 x
  · exact rowEval7777 x
  · exact rowEval7778 x
  · exact rowEval7779 x
  · exact rowEval7780 x
  · exact rowEval7781 x
  · exact rowEval7782 x
  · exact rowEval7783 x
  · exact rowEval7784 x
  · exact rowEval7785 x
  · exact rowEval7786 x
  · exact rowEval7787 x
  · exact rowEval7788 x
  · exact rowEval7789 x
  · exact rowEval8329 x
  · exact rowEval8330 x
  · exact rowEval8331 x
  · exact rowEval8332 x
  · exact rowEval8333 x
  · exact rowEval8334 x
  · exact rowEval8335 x
  · exact rowEval8336 x
  · exact rowEval8337 x
  · exact rowEval8338 x
  · exact rowEval8339 x
  · exact rowEval8340 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

def rows9_6 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8341, row8342, row8343, row8344, row8345, row8346, row8347, row8348, row8349, row8350, row8351, row8352, row8353, row8354, row8355, row8356, row8357, row8358, row8359, row8360, row8361, row8362, row8363, row8364, row8365, row8366, row8367, row8368, row8369, row8370, row8371, row8372, row8373, row8374, row8375, row8376]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8341 x
  · exact rowEval8342 x
  · exact rowEval8343 x
  · exact rowEval8344 x
  · exact rowEval8345 x
  · exact rowEval8346 x
  · exact rowEval8347 x
  · exact rowEval8348 x
  · exact rowEval8349 x
  · exact rowEval8350 x
  · exact rowEval8351 x
  · exact rowEval8352 x
  · exact rowEval8353 x
  · exact rowEval8354 x
  · exact rowEval8355 x
  · exact rowEval8356 x
  · exact rowEval8357 x
  · exact rowEval8358 x
  · exact rowEval8359 x
  · exact rowEval8360 x
  · exact rowEval8361 x
  · exact rowEval8362 x
  · exact rowEval8363 x
  · exact rowEval8364 x
  · exact rowEval8365 x
  · exact rowEval8366 x
  · exact rowEval8367 x
  · exact rowEval8368 x
  · exact rowEval8369 x
  · exact rowEval8370 x
  · exact rowEval8371 x
  · exact rowEval8372 x
  · exact rowEval8373 x
  · exact rowEval8374 x
  · exact rowEval8375 x
  · exact rowEval8376 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

def rows9_7 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8377, row8378, row8379, row8380, row8381, row8382, row8383, row8384, row8385, row8386, row8387, row8388, row8389, row8390, row8391, row8392, row8393, row8394, row8395, row8396, row8397, row8398, row8399, row8400, row8401, row8402, row8403, row8404, row8405, row8406, row8407, row8408, row8409, row8410, row8411, row8412]

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8377 x
  · exact rowEval8378 x
  · exact rowEval8379 x
  · exact rowEval8380 x
  · exact rowEval8381 x
  · exact rowEval8382 x
  · exact rowEval8383 x
  · exact rowEval8384 x
  · exact rowEval8385 x
  · exact rowEval8386 x
  · exact rowEval8387 x
  · exact rowEval8388 x
  · exact rowEval8389 x
  · exact rowEval8390 x
  · exact rowEval8391 x
  · exact rowEval8392 x
  · exact rowEval8393 x
  · exact rowEval8394 x
  · exact rowEval8395 x
  · exact rowEval8396 x
  · exact rowEval8397 x
  · exact rowEval8398 x
  · exact rowEval8399 x
  · exact rowEval8400 x
  · exact rowEval8401 x
  · exact rowEval8402 x
  · exact rowEval8403 x
  · exact rowEval8404 x
  · exact rowEval8405 x
  · exact rowEval8406 x
  · exact rowEval8407 x
  · exact rowEval8408 x
  · exact rowEval8409 x
  · exact rowEval8410 x
  · exact rowEval8411 x
  · exact rowEval8412 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

def rows9_8 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8413, row8414, row8415, row8416, row8417, row8418, row8419, row8420, row8421, row8422, row8423, row8424, row8425, row8426, row8427, row8428, row8429, row8430, row8431, row8432, row8433, row8434, row8435, row8436, row8437, row8438, row8439, row8440, row8441, row8442, row8443, row8444, row8445, row8446, row8447, row8448]

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8413 x
  · exact rowEval8414 x
  · exact rowEval8415 x
  · exact rowEval8416 x
  · exact rowEval8417 x
  · exact rowEval8418 x
  · exact rowEval8419 x
  · exact rowEval8420 x
  · exact rowEval8421 x
  · exact rowEval8422 x
  · exact rowEval8423 x
  · exact rowEval8424 x
  · exact rowEval8425 x
  · exact rowEval8426 x
  · exact rowEval8427 x
  · exact rowEval8428 x
  · exact rowEval8429 x
  · exact rowEval8430 x
  · exact rowEval8431 x
  · exact rowEval8432 x
  · exact rowEval8433 x
  · exact rowEval8434 x
  · exact rowEval8435 x
  · exact rowEval8436 x
  · exact rowEval8437 x
  · exact rowEval8438 x
  · exact rowEval8439 x
  · exact rowEval8440 x
  · exact rowEval8441 x
  · exact rowEval8442 x
  · exact rowEval8443 x
  · exact rowEval8444 x
  · exact rowEval8445 x
  · exact rowEval8446 x
  · exact rowEval8447 x
  · exact rowEval8448 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

def rows9_9 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row8449, row8450, row8451, row8452, row8453, row8454, row8455, row8456, row8457, row8458, row8459, row8460, row8461, row8462, row8463, row8464, row8465, row8466, row8467, row8468, row8469, row8470, row8471, row8472, row8473, row8474, row8475, row8476, row8477, row8478, row8479, row8480, row8481, row8482, row8483, row8484]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8449 x
  · exact rowEval8450 x
  · exact rowEval8451 x
  · exact rowEval8452 x
  · exact rowEval8453 x
  · exact rowEval8454 x
  · exact rowEval8455 x
  · exact rowEval8456 x
  · exact rowEval8457 x
  · exact rowEval8458 x
  · exact rowEval8459 x
  · exact rowEval8460 x
  · exact rowEval8461 x
  · exact rowEval8462 x
  · exact rowEval8463 x
  · exact rowEval8464 x
  · exact rowEval8465 x
  · exact rowEval8466 x
  · exact rowEval8467 x
  · exact rowEval8468 x
  · exact rowEval8469 x
  · exact rowEval8470 x
  · exact rowEval8471 x
  · exact rowEval8472 x
  · exact rowEval8473 x
  · exact rowEval8474 x
  · exact rowEval8475 x
  · exact rowEval8476 x
  · exact rowEval8477 x
  · exact rowEval8478 x
  · exact rowEval8479 x
  · exact rowEval8480 x
  · exact rowEval8481 x
  · exact rowEval8482 x
  · exact rowEval8483 x
  · exact rowEval8484 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block3.form9.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form9 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

end MUB6.Certificate.GramEntries.Block3

end OAI
