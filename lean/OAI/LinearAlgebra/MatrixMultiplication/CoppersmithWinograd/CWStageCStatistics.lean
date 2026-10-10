import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWCompleteStatistics
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCShapeProducts

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

def branchStatistic (s : Fin 3) (b : Fin 4) (i : Fin 3) : Fin 6 :=
  if i = s then if b.val < 2 then 3 else 2 else 1

theorem twoStatistic_of_side_weights (s : Fin 3) (b : Fin 4) (i : Fin 3)
    (w : Word)
    (hleft : CWLeafStatistics.weight (w 0) = branchAtom s b i)
    (hright : CWLeafStatistics.weight (w 1) = shape s i - branchAtom s b i) :
    CWCompleteStatistics.twoStatistic w = branchStatistic s b i := by
  change CWLeafStatistics.pairStatistic (w 0, w 1) = _
  unfold CWLeafStatistics.pairStatistic
  dsimp only
  rw [hleft, hright]
  fin_cases s <;> fin_cases b <;> fin_cases i <;> decide

theorem placed_twoStatistic_of_side_weights (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) (i : Fin 3) (w : Word)
    (hleft : CWLeafStatistics.weight (w 0) = branchAtom s b (phi.symm i))
    (hright : CWLeafStatistics.weight (w 1) =
      shape s (phi.symm i) - branchAtom s b (phi.symm i)) :
    CWCompleteStatistics.twoStatistic w = branchStatistic s b (phi.symm i) :=
  twoStatistic_of_side_weights s b (phi.symm i) w hleft hright

theorem wordPopulation_of_branchStatistic (counts : Fin 4 → ℕ) (s i : Fin 3)
    (w : Positions counts → Fin 6)
    (hw : ∀ p, w p = branchStatistic s p.1 i) (a : Fin 6) :
    wordPopulation w a =
      ∑ b : Fin 4, if branchStatistic s b i = a then counts b else 0 := by
  let e : {p : Positions counts // w p = a} ≃
      (Σ b : Fin 4, {j : Fin (counts b) // branchStatistic s b i = a}) :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, (hw p.val).symm.trans p.property⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.val⟩, (hw _).trans p.2.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  rw [wordPopulation, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : branchStatistic s b i = a <;> simp [h]

theorem empiricalLaw_eq_littleLaw (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true) (n : ℕ) (hn : 0 < n)
    (hc : ∀ b, (counts b : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u b)
    (i : Fin 3) (w : Positions counts → Fin 6)
    (hw : ∀ p, w p = branchStatistic (AllFieldHistory.stageCDistinguished u) p.1 i) :
    InheritedMasks.empiricalLaw w =
      fun a => (AllFieldParameters.littleLaw t u i a : ℝ) := by
  have hcard : Fintype.card (Positions counts) = n := by
    apply Nat.cast_injective (R := ℚ)
    calc
      (Fintype.card (Positions counts) : ℚ) = ∑ b, (counts b : ℚ) := by
        simp [Positions, Fintype.card_sigma]
      _ = n := by
        simp only [hc, ← Finset.mul_sum, AllFieldHistory.stageCWeight_normalized, mul_one]
  have hshape : u i = if i = AllFieldHistory.stageCDistinguished u then 2 else 1 := by
    exact congrFun (shape_eq_parent u hu hpos).symm i
  have hcount (a : Fin 6) : (wordPopulation w a : ℚ) =
      (n : ℚ) * AllFieldParameters.littleLaw t u i a := by
    rw [wordPopulation_of_branchStatistic counts _ i w hw a]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    simp_rw [hc]
    simp only [AllFieldParameters.littleLaw, hshape]
    by_cases hi : i = AllFieldHistory.stageCDistinguished u <;>
      fin_cases a <;>
      simp [branchStatistic, hi, Fin.sum_univ_succ,
        AllFieldParameters.singletonSlot,
        AllFieldHistory.stageCWeight] <;> ring
  funext a
  have hr : (wordPopulation w a : ℝ) =
      (n : ℝ) * (AllFieldParameters.littleLaw t u i a : ℝ) := by
    exact_mod_cast hcount a
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [InheritedMasks.empiricalLaw, hr, hcard]
  exact mul_div_cancel_left₀ _ hn'

theorem typeWindow_of_placed_side_weights (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true) (n : ℕ) (hn : 0 < n)
    (hc : ∀ b, (counts b : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u b)
    (phi : Equiv.Perm (Fin 3)) (i : Fin 3) (w : Positions counts → Word)
    (hweights : ∀ p,
      CWLeafStatistics.weight (w p 0) =
        branchAtom (AllFieldHistory.stageCDistinguished u) p.1 (phi.symm i) ∧
      CWLeafStatistics.weight (w p 1) =
        shape (AllFieldHistory.stageCDistinguished u) (phi.symm i) -
          branchAtom (AllFieldHistory.stageCDistinguished u) p.1 (phi.symm i))
    (η : ℝ) (hη : 0 ≤ η) :
    InheritedMasks.typeWindow
      (fun a : Fin 6 => (AllFieldParameters.littleLaw t u (phi.symm i) a : ℝ)) η
      (fun p => CWCompleteStatistics.twoStatistic (w p)) := by
  have he := empiricalLaw_eq_littleLaw counts t u hu hpos n hn hc (phi.symm i)
    (fun p => CWCompleteStatistics.twoStatistic (w p)) (fun p =>
      twoStatistic_of_side_weights _ _ _ _ (hweights p).1 (hweights p).2)
  intro a
  rw [he]
  simpa only [sub_self, abs_zero] using hη

theorem placedChildProducts_support_typeWindow (F : Type*) [CommRing F]
    (counts : Fin 4 → ℕ) (t u : AllFieldParameters.Shape)
    (hu : u ∈ AllFieldParameters.shapes 4) (hpos : AllFieldParameters.positive u = true)
    (n : ℕ) (hn : 0 < n)
    (hc : ∀ b, (counts b : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u b)
    (phi : Equiv.Perm (Fin 3)) (x y z : Positions counts → ChildPair)
    (hne : placedChildProducts F (AllFieldHistory.stageCDistinguished u) phi counts x y z ≠ 0)
    (i : Fin 3) (η : ℝ) (hη : 0 ≤ η) :
    InheritedMasks.typeWindow
      (fun a : Fin 6 => (AllFieldParameters.littleLaw t u (phi.symm i) a : ℝ)) η
      (fun p => CWCompleteStatistics.twoStatistic (joinChildren (![x p, y p, z p] i))) := by
  apply typeWindow_of_placed_side_weights counts t u hu hpos n hn hc phi i
    (fun p => joinChildren (![x p, y p, z p] i)) _ η hη
  intro p
  exact placedChildProducts_side_weights F _ phi counts x y z hne p i

theorem placedShapeChildProducts_support_typeWindow (F : Type*) [CommRing F]
    (counts : Fin 4 → ℕ) (t u : AllFieldParameters.Shape)
    (hu : u ∈ AllFieldParameters.shapes 4) (hpos : AllFieldParameters.positive u = true)
    (n : ℕ) (hn : 0 < n)
    (hc : ∀ b, (counts b : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u b)
    (phi : Equiv.Perm (Fin 3)) (x y z : Positions counts → ChildWords)
    (hne : placedShapeChildProducts F (AllFieldHistory.stageCDistinguished u)
      phi counts x y z ≠ 0)
    (i : Fin 3) (η : ℝ) (hη : 0 ≤ η) :
    InheritedMasks.typeWindow
      (fun a : Fin 6 => (AllFieldParameters.littleLaw t u (phi.symm i) a : ℝ)) η
      (fun p => CWCompleteStatistics.twoStatistic
        (joinChildren (collapseChildWords (![x p, y p, z p] i)))) := by
  have hcollapse : placedChildProducts F (AllFieldHistory.stageCDistinguished u)
      phi counts (collapseChildWords ∘ x) (collapseChildWords ∘ y)
        (collapseChildWords ∘ z) ≠ 0 := by
    rw [placedShapeChildProducts_collapse]
    exact hne
  have hwindow := placedChildProducts_support_typeWindow F counts t u hu hpos n hn hc
    phi (collapseChildWords ∘ x) (collapseChildWords ∘ y) (collapseChildWords ∘ z)
    hcollapse i η hη
  fin_cases i <;> exact hwindow

end MatrixMultiplication.CWStageCProducts

end

end OAI
