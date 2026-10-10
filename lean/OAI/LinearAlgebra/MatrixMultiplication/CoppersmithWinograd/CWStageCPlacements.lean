import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCProducts
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCLaw

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def atomPermutation (s : Fin 3) (phi : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  if phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0 then Equiv.refl _
  else Equiv.swap 2 3

theorem branchAtom_transport (s : Fin 3) (phi : Equiv.Perm (Fin 3))
    (b : Fin 4) (i : Fin 3) :
    branchAtom (phi s) (atomPermutation s phi b) (phi i) = branchAtom s b i := by
  have h01 : phi 0 ≠ phi 1 := phi.injective.ne (by decide)
  have h02 : phi 0 ≠ phi 2 := phi.injective.ne (by decide)
  have h12 : phi 1 ≠ phi 2 := phi.injective.ne (by decide)
  generalize hp0 : phi 0 = p0 at *
  generalize hp1 : phi 1 = p1 at *
  generalize hp2 : phi 2 = p2 at *
  fin_cases p0 <;> fin_cases p1 <;> fin_cases p2 <;> simp_all only [ne_eq,
    not_false_eq_true, not_true_eq_false]
  all_goals fin_cases s <;> fin_cases b <;> fin_cases i <;>
    simp [atomPermutation, branchAtom, canonicalAtom, Equiv.swap_apply_def, hp0, hp1, hp2]

theorem atomPermutation_single (s : Fin 3) (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    (atomPermutation s phi b).val < 2 ↔ b.val < 2 := by
  unfold atomPermutation
  split_ifs
  · rfl
  · fin_cases b <;> decide

theorem branchAtom_eq_stageCAtom (u : AllFieldParameters.Shape) (b : Fin 4) :
    branchAtom (AllFieldHistory.stageCDistinguished u) b = AllFieldHistory.stageCAtom u b := by
  rfl

theorem shape_eq_parent (u : AllFieldParameters.Shape)
    (hu : u ∈ AllFieldParameters.shapes 4) (hpos : AllFieldParameters.positive u = true) :
    shape (AllFieldHistory.stageCDistinguished u) = u := by
  rcases AllFieldHistory.positive_four_shapes u hu hpos with rfl | rfl | rfl <;>
    funext i <;> fin_cases i <;> rfl

theorem shape_transport (s : Fin 3) (phi : Equiv.Perm (Fin 3)) (i : Fin 3) :
    shape (phi s) i = shape s (phi.symm i) := by
  have hiff : i = phi s ↔ phi.symm i = s := by
    constructor
    · intro h
      simp only [h, Equiv.symm_apply_apply]
    · intro h
      have hh := congrArg phi h
      simpa only [Equiv.apply_symm_apply] using hh
  simp only [shape, hiff]

def placedBranchSource (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) : Tensor F Word Word Word :=
  fun x y z =>
    if CWLeafStatistics.weight (x 0) = branchAtom s b (phi.symm 0) ∧
      CWLeafStatistics.weight (y 0) = branchAtom s b (phi.symm 1) ∧
      CWLeafStatistics.weight (z 0) = branchAtom s b (phi.symm 2)
    then source F (phi s) x y z else 0

theorem placedBranchSource_eq (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedBranchSource F s phi b = branchSource F (phi s) (atomPermutation s phi b) := by
  have h0 := branchAtom_transport s phi b (phi.symm 0)
  have h1 := branchAtom_transport s phi b (phi.symm 1)
  have h2 := branchAtom_transport s phi b (phi.symm 2)
  simp only [Equiv.apply_symm_apply] at h0 h1 h2
  funext x y z
  simp only [placedBranchSource, branchSource, h0, h1, h2]

theorem placed_branch_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    ∃ (a : (Row (phi s) b × Middle (phi s) b) → Word → F)
      (c : (Middle (phi s) b × Column (phi s) b) → Word → F)
      (e : (Column (phi s) b × Row (phi s) b) → Word → F),
      Tensor.restrict a c e (placedBranchSource F s phi b) =
        Tensor.matrixCoefficients (Row (phi s) b) (Middle (phi s) b) (Column (phi s) b) := by
  rw [placedBranchSource_eq]
  have h := oriented_restriction F (phi s) (atomPermutation s phi b)
  by_cases hp : phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0
  · have he : atomPermutation s phi = Equiv.refl _ := by simp [atomPermutation, hp]
    rw [he] at h ⊢
    exact h
  · have he : atomPermutation s phi = Equiv.swap 2 3 := by simp [atomPermutation, hp]
    rw [he] at h ⊢
    fin_cases b <;> exact h

def placedProductSource (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    Tensor F (Positions counts → Word) (Positions counts → Word) (Positions counts → Word) :=
  CommonDimensions.familyProduct (fun p : Positions counts => placedBranchSource F s phi p.1)

theorem placed_product_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    ∃ (a : (RowWords (phi s) counts × MiddleWords (phi s) counts) →
        (Positions counts → Word) → F)
      (c : (MiddleWords (phi s) counts × ColumnWords (phi s) counts) →
        (Positions counts → Word) → F)
      (e : (ColumnWords (phi s) counts × RowWords (phi s) counts) →
        (Positions counts → Word) → F),
      Tensor.restrict a c e (placedProductSource F s phi counts) =
        Tensor.matrixCoefficients (RowWords (phi s) counts) (MiddleWords (phi s) counts)
          (ColumnWords (phi s) counts) := by
  classical
  choose a c e h using fun p : Positions counts => placed_branch_restriction F s phi p.1
  exact TerminalProducts.matrix_restriction_of_history_restrictions
    (fun p : Positions counts => placedBranchSource F s phi p.1)
    (fun p => Row (phi s) p.1) (fun p => Middle (phi s) p.1)
    (fun p => Column (phi s) p.1) a c e h

end MatrixMultiplication.CWStageCProducts

end

end OAI
