import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block59
import OAI.Analysis.MutuallyUnbiased.GramRows.Block60
import OAI.Analysis.MutuallyUnbiased.GramRows.Block61

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4556, row4557, row4558, row4559, row4560, row4561, row4562, row4563, row4564, row4565, row4566, row4567, row4568, row4569]

theorem entryCheck19_0 : entry19_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_0 k)) := by decide +kernel

theorem rowsSound19_0 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval4556 x
  · exact rowEval4557 x
  · exact rowEval4558 x
  · exact rowEval4559 x
  · exact rowEval4560 x
  · exact rowEval4561 x
  · exact rowEval4562 x
  · exact rowEval4563 x
  · exact rowEval4564 x
  · exact rowEval4565 x
  · exact rowEval4566 x
  · exact rowEval4567 x
  · exact rowEval4568 x
  · exact rowEval4569 x

theorem entryEval19_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_0 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck19_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_0]

def rows19_1 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4570, row4571, row4572, row4573, row4574, row4575, row4576, row4577, row4578, row4579, row4580, row4581, row4582, row4583]

theorem entryCheck19_1 : entry19_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_1 k)) := by decide +kernel

theorem rowsSound19_1 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval4570 x
  · exact rowEval4571 x
  · exact rowEval4572 x
  · exact rowEval4573 x
  · exact rowEval4574 x
  · exact rowEval4575 x
  · exact rowEval4576 x
  · exact rowEval4577 x
  · exact rowEval4578 x
  · exact rowEval4579 x
  · exact rowEval4580 x
  · exact rowEval4581 x
  · exact rowEval4582 x
  · exact rowEval4583 x

theorem entryEval19_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_1 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck19_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_1]

def rows19_2 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4584, row4585, row4586, row4587, row4588, row4589, row4590, row4591, row4592, row4593, row4594, row4595, row4596, row4597]

theorem entryCheck19_2 : entry19_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_2 k)) := by decide +kernel

theorem rowsSound19_2 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval4584 x
  · exact rowEval4585 x
  · exact rowEval4586 x
  · exact rowEval4587 x
  · exact rowEval4588 x
  · exact rowEval4589 x
  · exact rowEval4590 x
  · exact rowEval4591 x
  · exact rowEval4592 x
  · exact rowEval4593 x
  · exact rowEval4594 x
  · exact rowEval4595 x
  · exact rowEval4596 x
  · exact rowEval4597 x

theorem entryEval19_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_2 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck19_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_2]

def rows19_3 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4598, row4599, row4600, row4601, row4602, row4603, row4604, row4605, row4606, row4607, row4608, row4609, row4610, row4611]

theorem entryCheck19_3 : entry19_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_3 k)) := by decide +kernel

theorem rowsSound19_3 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval4598 x
  · exact rowEval4599 x
  · exact rowEval4600 x
  · exact rowEval4601 x
  · exact rowEval4602 x
  · exact rowEval4603 x
  · exact rowEval4604 x
  · exact rowEval4605 x
  · exact rowEval4606 x
  · exact rowEval4607 x
  · exact rowEval4608 x
  · exact rowEval4609 x
  · exact rowEval4610 x
  · exact rowEval4611 x

theorem entryEval19_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_3 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck19_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_3]

def rows19_4 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4612, row4613, row4614, row4615, row4616, row4617, row4618, row4619, row4620, row4621, row4622, row4623, row4624, row4625]

theorem entryCheck19_4 : entry19_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_4 k)) := by decide +kernel

theorem rowsSound19_4 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval4612 x
  · exact rowEval4613 x
  · exact rowEval4614 x
  · exact rowEval4615 x
  · exact rowEval4616 x
  · exact rowEval4617 x
  · exact rowEval4618 x
  · exact rowEval4619 x
  · exact rowEval4620 x
  · exact rowEval4621 x
  · exact rowEval4622 x
  · exact rowEval4623 x
  · exact rowEval4624 x
  · exact rowEval4625 x

theorem entryEval19_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_4 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck19_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_4]

def rows19_5 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4626, row4627, row4628, row4629, row4630, row4631, row4632, row4633, row4634, row4635, row4636, row4637, row4638, row4639]

theorem entryCheck19_5 : entry19_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_5 k)) := by decide +kernel

theorem rowsSound19_5 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval4626 x
  · exact rowEval4627 x
  · exact rowEval4628 x
  · exact rowEval4629 x
  · exact rowEval4630 x
  · exact rowEval4631 x
  · exact rowEval4632 x
  · exact rowEval4633 x
  · exact rowEval4634 x
  · exact rowEval4635 x
  · exact rowEval4636 x
  · exact rowEval4637 x
  · exact rowEval4638 x
  · exact rowEval4639 x

theorem entryEval19_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_5 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck19_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_5]

def rows19_6 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4640, row4641, row4642, row4643, row4644, row4645, row4646, row4647, row4648, row4649, row4650, row4651, row4652, row4653]

theorem entryCheck19_6 : entry19_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_6 k)) := by decide +kernel

theorem rowsSound19_6 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval4640 x
  · exact rowEval4641 x
  · exact rowEval4642 x
  · exact rowEval4643 x
  · exact rowEval4644 x
  · exact rowEval4645 x
  · exact rowEval4646 x
  · exact rowEval4647 x
  · exact rowEval4648 x
  · exact rowEval4649 x
  · exact rowEval4650 x
  · exact rowEval4651 x
  · exact rowEval4652 x
  · exact rowEval4653 x

theorem entryEval19_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_6 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck19_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_6]

def rows19_7 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4654, row4655, row4656, row4657, row4658, row4659, row4660, row4661, row4662, row4663, row4664, row4665, row4666, row4667]

theorem entryCheck19_7 : entry19_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_7 k)) := by decide +kernel

theorem rowsSound19_7 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval4654 x
  · exact rowEval4655 x
  · exact rowEval4656 x
  · exact rowEval4657 x
  · exact rowEval4658 x
  · exact rowEval4659 x
  · exact rowEval4660 x
  · exact rowEval4661 x
  · exact rowEval4662 x
  · exact rowEval4663 x
  · exact rowEval4664 x
  · exact rowEval4665 x
  · exact rowEval4666 x
  · exact rowEval4667 x

theorem entryEval19_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_7 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck19_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_7]

def rows19_8 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4668, row4669, row4670, row4671, row4672, row4673, row4674, row4675, row4676, row4677, row4678, row4679, row4680, row4681]

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval4668 x
  · exact rowEval4669 x
  · exact rowEval4670 x
  · exact rowEval4671 x
  · exact rowEval4672 x
  · exact rowEval4673 x
  · exact rowEval4674 x
  · exact rowEval4675 x
  · exact rowEval4676 x
  · exact rowEval4677 x
  · exact rowEval4678 x
  · exact rowEval4679 x
  · exact rowEval4680 x
  · exact rowEval4681 x

theorem entryEval19_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

def rows19_9 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4682, row4683, row4684, row4685, row4686, row4687, row4688, row4689, row4690, row4691, row4692, row4693, row4694, row4695]

theorem entryCheck19_9 : entry19_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_9 k)) := by decide +kernel

theorem rowsSound19_9 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval4682 x
  · exact rowEval4683 x
  · exact rowEval4684 x
  · exact rowEval4685 x
  · exact rowEval4686 x
  · exact rowEval4687 x
  · exact rowEval4688 x
  · exact rowEval4689 x
  · exact rowEval4690 x
  · exact rowEval4691 x
  · exact rowEval4692 x
  · exact rowEval4693 x
  · exact rowEval4694 x
  · exact rowEval4695 x

theorem entryEval19_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_9 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck19_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_9]

def rows19_10 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4696, row4697, row4698, row4699, row4700, row4701, row4702, row4703, row4704, row4705, row4706, row4707, row4708, row4709]

theorem entryCheck19_10 : entry19_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_10 k)) := by decide +kernel

theorem rowsSound19_10 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4696 x
  · exact rowEval4697 x
  · exact rowEval4698 x
  · exact rowEval4699 x
  · exact rowEval4700 x
  · exact rowEval4701 x
  · exact rowEval4702 x
  · exact rowEval4703 x
  · exact rowEval4704 x
  · exact rowEval4705 x
  · exact rowEval4706 x
  · exact rowEval4707 x
  · exact rowEval4708 x
  · exact rowEval4709 x

theorem entryEval19_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_10 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck19_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_10]

def rows19_11 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4710, row4711, row4712, row4713, row4714, row4715, row4716, row4717, row4718, row4719, row4720, row4721, row4722, row4723]

theorem entryCheck19_11 : entry19_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_11 k)) := by decide +kernel

theorem rowsSound19_11 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4710 x
  · exact rowEval4711 x
  · exact rowEval4712 x
  · exact rowEval4713 x
  · exact rowEval4714 x
  · exact rowEval4715 x
  · exact rowEval4716 x
  · exact rowEval4717 x
  · exact rowEval4718 x
  · exact rowEval4719 x
  · exact rowEval4720 x
  · exact rowEval4721 x
  · exact rowEval4722 x
  · exact rowEval4723 x

theorem entryEval19_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_11 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck19_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_11]

def rows19_12 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4724, row4725, row4726, row4727, row4728, row4729, row4730, row4731, row4732, row4733, row4734, row4735, row4736, row4737]

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

theorem rowsSound19_12 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4724 x
  · exact rowEval4725 x
  · exact rowEval4726 x
  · exact rowEval4727 x
  · exact rowEval4728 x
  · exact rowEval4729 x
  · exact rowEval4730 x
  · exact rowEval4731 x
  · exact rowEval4732 x
  · exact rowEval4733 x
  · exact rowEval4734 x
  · exact rowEval4735 x
  · exact rowEval4736 x
  · exact rowEval4737 x

theorem entryEval19_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_12 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck19_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_12]

def rows19_13 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4738, row4739, row4740, row4741, row4742, row4743, row4744, row4745, row4746, row4747, row4748, row4749, row4750, row4751]

theorem entryCheck19_13 : entry19_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_13 k)) := by decide +kernel

theorem rowsSound19_13 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval4738 x
  · exact rowEval4739 x
  · exact rowEval4740 x
  · exact rowEval4741 x
  · exact rowEval4742 x
  · exact rowEval4743 x
  · exact rowEval4744 x
  · exact rowEval4745 x
  · exact rowEval4746 x
  · exact rowEval4747 x
  · exact rowEval4748 x
  · exact rowEval4749 x
  · exact rowEval4750 x
  · exact rowEval4751 x

theorem entryEval19_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_13 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck19_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_13]

def rows19_14 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4752, row4753, row4754, row4755, row4756, row4757, row4758, row4759, row4760, row4761, row4762, row4763, row4764, row4765]

theorem entryCheck19_14 : entry19_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_14 k)) := by decide +kernel

theorem rowsSound19_14 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval4752 x
  · exact rowEval4753 x
  · exact rowEval4754 x
  · exact rowEval4755 x
  · exact rowEval4756 x
  · exact rowEval4757 x
  · exact rowEval4758 x
  · exact rowEval4759 x
  · exact rowEval4760 x
  · exact rowEval4761 x
  · exact rowEval4762 x
  · exact rowEval4763 x
  · exact rowEval4764 x
  · exact rowEval4765 x

theorem entryEval19_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_14 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck19_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_14]

def rows19_15 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4766, row4767, row4768, row4769, row4770, row4771, row4772, row4773, row4774, row4775, row4776, row4777, row4778, row4779]

theorem entryCheck19_15 : entry19_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_15 k)) := by decide +kernel

theorem rowsSound19_15 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval4766 x
  · exact rowEval4767 x
  · exact rowEval4768 x
  · exact rowEval4769 x
  · exact rowEval4770 x
  · exact rowEval4771 x
  · exact rowEval4772 x
  · exact rowEval4773 x
  · exact rowEval4774 x
  · exact rowEval4775 x
  · exact rowEval4776 x
  · exact rowEval4777 x
  · exact rowEval4778 x
  · exact rowEval4779 x

theorem entryEval19_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_15 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck19_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_15]

def rows19_16 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4780, row4781, row4782, row4783, row4784, row4785, row4786, row4787, row4788, row4789, row4790, row4791, row4792, row4793]

theorem entryCheck19_16 : entry19_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_16 k)) := by decide +kernel

theorem rowsSound19_16 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval4780 x
  · exact rowEval4781 x
  · exact rowEval4782 x
  · exact rowEval4783 x
  · exact rowEval4784 x
  · exact rowEval4785 x
  · exact rowEval4786 x
  · exact rowEval4787 x
  · exact rowEval4788 x
  · exact rowEval4789 x
  · exact rowEval4790 x
  · exact rowEval4791 x
  · exact rowEval4792 x
  · exact rowEval4793 x

theorem entryEval19_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_16 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck19_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_16]

def rows19_17 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4794, row4795, row4796, row4797, row4798, row4799, row4800, row4801, row4802, row4803, row4804, row4805, row4806, row4807]

theorem entryCheck19_17 : entry19_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_17 k)) := by decide +kernel

theorem rowsSound19_17 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form17) x := by
  fin_cases k
  · exact rowEval4794 x
  · exact rowEval4795 x
  · exact rowEval4796 x
  · exact rowEval4797 x
  · exact rowEval4798 x
  · exact rowEval4799 x
  · exact rowEval4800 x
  · exact rowEval4801 x
  · exact rowEval4802 x
  · exact rowEval4803 x
  · exact rowEval4804 x
  · exact rowEval4805 x
  · exact rowEval4806 x
  · exact rowEval4807 x

theorem entryEval19_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_17 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form17 B := by
  rw [entryCheck19_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_17]

def rows19_18 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4808, row4809, row4810, row4811, row4812, row4813, row4814, row4815, row4816, row4817, row4818, row4819, row4820, row4821]

theorem entryCheck19_18 : entry19_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_18 k)) := by decide +kernel

theorem rowsSound19_18 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form18) x := by
  fin_cases k
  · exact rowEval4808 x
  · exact rowEval4809 x
  · exact rowEval4810 x
  · exact rowEval4811 x
  · exact rowEval4812 x
  · exact rowEval4813 x
  · exact rowEval4814 x
  · exact rowEval4815 x
  · exact rowEval4816 x
  · exact rowEval4817 x
  · exact rowEval4818 x
  · exact rowEval4819 x
  · exact rowEval4820 x
  · exact rowEval4821 x

theorem entryEval19_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_18 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form18 B := by
  rw [entryCheck19_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_18]

def rows19_19 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4822, row4823, row4824, row4825, row4826, row4827, row4828, row4829, row4830, row4831, row4832, row4833, row4834, row4835]

theorem entryCheck19_19 : entry19_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form19.terms k).coefficient) (rows19_19 k)) := by decide +kernel

theorem rowsSound19_19 (k : Fin GramFunctions.Block1.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form19.terms k).tag (GramFunctions.Block1.form19.terms k).charge GramFunctions.Block1.form19) x := by
  fin_cases k
  · exact rowEval4822 x
  · exact rowEval4823 x
  · exact rowEval4824 x
  · exact rowEval4825 x
  · exact rowEval4826 x
  · exact rowEval4827 x
  · exact rowEval4828 x
  · exact rowEval4829 x
  · exact rowEval4830 x
  · exact rowEval4831 x
  · exact rowEval4832 x
  · exact rowEval4833 x
  · exact rowEval4834 x
  · exact rowEval4835 x

theorem entryEval19_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_19 (GramNormalization.eval B) = GramFunctions.Block1.form19.mixedGram GramFunctions.Block1.form19 B := by
  rw [entryCheck19_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form19 GramFunctions.Block1.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_19]

end MUB6.Certificate.GramEntries.Block1

end OAI
