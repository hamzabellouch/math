import OAI.Analysis.MutuallyUnbiased.GramEntries.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block168
import OAI.Analysis.MutuallyUnbiased.GramRows.Block169

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block5.form2.size → Integer.Sparse Key := ![row18459, row18460, row18461, row18462, row18463, row18464, row18465, row18466, row18467, row18468, row18469, row18470, row18471, row18472, row18473, row18474, row18475, row18476, row18477, row18478, row18479, row18480, row18481, row18482, row18483, row18484, row18485, row18486, row18487, row18488, row18489, row18490, row18491, row18492, row18493, row18494, row18495, row18496, row18497, row18498, row18499, row18500, row18501, row18502, row18503, row18504, row18505, row18506, row18507, row18508, row18509, row18510, row18511, row18512, row18513, row18514, row18515, row18516, row18517, row18518]

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block5.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form2.terms k).tag (GramFunctions.Block5.form2.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18459 x
  · exact rowEval18460 x
  · exact rowEval18461 x
  · exact rowEval18462 x
  · exact rowEval18463 x
  · exact rowEval18464 x
  · exact rowEval18465 x
  · exact rowEval18466 x
  · exact rowEval18467 x
  · exact rowEval18468 x
  · exact rowEval18469 x
  · exact rowEval18470 x
  · exact rowEval18471 x
  · exact rowEval18472 x
  · exact rowEval18473 x
  · exact rowEval18474 x
  · exact rowEval18475 x
  · exact rowEval18476 x
  · exact rowEval18477 x
  · exact rowEval18478 x
  · exact rowEval18479 x
  · exact rowEval18480 x
  · exact rowEval18481 x
  · exact rowEval18482 x
  · exact rowEval18483 x
  · exact rowEval18484 x
  · exact rowEval18485 x
  · exact rowEval18486 x
  · exact rowEval18487 x
  · exact rowEval18488 x
  · exact rowEval18489 x
  · exact rowEval18490 x
  · exact rowEval18491 x
  · exact rowEval18492 x
  · exact rowEval18493 x
  · exact rowEval18494 x
  · exact rowEval18495 x
  · exact rowEval18496 x
  · exact rowEval18497 x
  · exact rowEval18498 x
  · exact rowEval18499 x
  · exact rowEval18500 x
  · exact rowEval18501 x
  · exact rowEval18502 x
  · exact rowEval18503 x
  · exact rowEval18504 x
  · exact rowEval18505 x
  · exact rowEval18506 x
  · exact rowEval18507 x
  · exact rowEval18508 x
  · exact rowEval18509 x
  · exact rowEval18510 x
  · exact rowEval18511 x
  · exact rowEval18512 x
  · exact rowEval18513 x
  · exact rowEval18514 x
  · exact rowEval18515 x
  · exact rowEval18516 x
  · exact rowEval18517 x
  · exact rowEval18518 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block5.form2.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form2 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

def rows2_1 : Fin GramFunctions.Block5.form2.size → Integer.Sparse Key := ![row18519, row18520, row18521, row18522, row18523, row18524, row18525, row18526, row18527, row18528, row18529, row18530, row18531, row18532, row18533, row18534, row18535, row18536, row18537, row18538, row18539, row18540, row18541, row18542, row18543, row18544, row18545, row18546, row18547, row18548, row18549, row18550, row18551, row18552, row18553, row18554, row18555, row18556, row18557, row18558, row18559, row18560, row18561, row18562, row18563, row18564, row18565, row18566, row18567, row18568, row18569, row18570, row18571, row18572, row18573, row18574, row18575, row18576, row18577, row18578]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block5.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form2.terms k).tag (GramFunctions.Block5.form2.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval18519 x
  · exact rowEval18520 x
  · exact rowEval18521 x
  · exact rowEval18522 x
  · exact rowEval18523 x
  · exact rowEval18524 x
  · exact rowEval18525 x
  · exact rowEval18526 x
  · exact rowEval18527 x
  · exact rowEval18528 x
  · exact rowEval18529 x
  · exact rowEval18530 x
  · exact rowEval18531 x
  · exact rowEval18532 x
  · exact rowEval18533 x
  · exact rowEval18534 x
  · exact rowEval18535 x
  · exact rowEval18536 x
  · exact rowEval18537 x
  · exact rowEval18538 x
  · exact rowEval18539 x
  · exact rowEval18540 x
  · exact rowEval18541 x
  · exact rowEval18542 x
  · exact rowEval18543 x
  · exact rowEval18544 x
  · exact rowEval18545 x
  · exact rowEval18546 x
  · exact rowEval18547 x
  · exact rowEval18548 x
  · exact rowEval18549 x
  · exact rowEval18550 x
  · exact rowEval18551 x
  · exact rowEval18552 x
  · exact rowEval18553 x
  · exact rowEval18554 x
  · exact rowEval18555 x
  · exact rowEval18556 x
  · exact rowEval18557 x
  · exact rowEval18558 x
  · exact rowEval18559 x
  · exact rowEval18560 x
  · exact rowEval18561 x
  · exact rowEval18562 x
  · exact rowEval18563 x
  · exact rowEval18564 x
  · exact rowEval18565 x
  · exact rowEval18566 x
  · exact rowEval18567 x
  · exact rowEval18568 x
  · exact rowEval18569 x
  · exact rowEval18570 x
  · exact rowEval18571 x
  · exact rowEval18572 x
  · exact rowEval18573 x
  · exact rowEval18574 x
  · exact rowEval18575 x
  · exact rowEval18576 x
  · exact rowEval18577 x
  · exact rowEval18578 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block5.form2.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form2 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

def rows2_2 : Fin GramFunctions.Block5.form2.size → Integer.Sparse Key := ![row18579, row18580, row18581, row18582, row18583, row18584, row18585, row18586, row18587, row18588, row18589, row18590, row18591, row18592, row18593, row18594, row18595, row18596, row18597, row18598, row18599, row18600, row18601, row18602, row18603, row18604, row18605, row18606, row18607, row18608, row18609, row18610, row18611, row18612, row18613, row18614, row18615, row18616, row18617, row18618, row18619, row18620, row18621, row18622, row18623, row18624, row18625, row18626, row18627, row18628, row18629, row18630, row18631, row18632, row18633, row18634, row18635, row18636, row18637, row18638]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block5.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form2.terms k).tag (GramFunctions.Block5.form2.terms k).charge GramFunctions.Block5.form2) x := by
  fin_cases k
  · exact rowEval18579 x
  · exact rowEval18580 x
  · exact rowEval18581 x
  · exact rowEval18582 x
  · exact rowEval18583 x
  · exact rowEval18584 x
  · exact rowEval18585 x
  · exact rowEval18586 x
  · exact rowEval18587 x
  · exact rowEval18588 x
  · exact rowEval18589 x
  · exact rowEval18590 x
  · exact rowEval18591 x
  · exact rowEval18592 x
  · exact rowEval18593 x
  · exact rowEval18594 x
  · exact rowEval18595 x
  · exact rowEval18596 x
  · exact rowEval18597 x
  · exact rowEval18598 x
  · exact rowEval18599 x
  · exact rowEval18600 x
  · exact rowEval18601 x
  · exact rowEval18602 x
  · exact rowEval18603 x
  · exact rowEval18604 x
  · exact rowEval18605 x
  · exact rowEval18606 x
  · exact rowEval18607 x
  · exact rowEval18608 x
  · exact rowEval18609 x
  · exact rowEval18610 x
  · exact rowEval18611 x
  · exact rowEval18612 x
  · exact rowEval18613 x
  · exact rowEval18614 x
  · exact rowEval18615 x
  · exact rowEval18616 x
  · exact rowEval18617 x
  · exact rowEval18618 x
  · exact rowEval18619 x
  · exact rowEval18620 x
  · exact rowEval18621 x
  · exact rowEval18622 x
  · exact rowEval18623 x
  · exact rowEval18624 x
  · exact rowEval18625 x
  · exact rowEval18626 x
  · exact rowEval18627 x
  · exact rowEval18628 x
  · exact rowEval18629 x
  · exact rowEval18630 x
  · exact rowEval18631 x
  · exact rowEval18632 x
  · exact rowEval18633 x
  · exact rowEval18634 x
  · exact rowEval18635 x
  · exact rowEval18636 x
  · exact rowEval18637 x
  · exact rowEval18638 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block5.form2.mixedGram GramFunctions.Block5.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form2 GramFunctions.Block5.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block5

end OAI
