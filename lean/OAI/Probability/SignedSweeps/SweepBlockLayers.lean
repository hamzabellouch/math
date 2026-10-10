import OAI.Probability.SignedSweeps.ProvedRanges4
import OAI.Probability.SignedSweeps.CoefficientUniform

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) sweepBlockLayersFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def columnEnumeration (a b : ℕ) : (Σ _ : Fin (2^b), Fin (2^a)) ≃ Fin (2^(a+b)) :=
  (Equiv.sigmaEquivProd (Fin (2^b)) (Fin (2^a))).trans
    ((Equiv.prodComm _ _).trans (sweepBoard a b).symm)

def rowEnumeration (a b : ℕ) : (Σ _ : Fin (2^a), Fin (2^b)) ≃ Fin (2^(a+b)) :=
  (Equiv.sigmaEquivProd (Fin (2^a)) (Fin (2^b))).trans (sweepBoard a b).symm

@[simp] lemma columnEnumeration_board (a b : ℕ) (j : Fin (2^b)) (x : Fin (2^a)) :
    sweepBoard a b (columnEnumeration a b ⟨j,x⟩) = (x,j) := by
  simp [columnEnumeration]

@[simp] lemma rowEnumeration_board (a b : ℕ) (i : Fin (2^a)) (x : Fin (2^b)) :
    sweepBoard a b (rowEnumeration a b ⟨i,x⟩) = (i,x) := by
  simp [rowEnumeration]

lemma columnEnumeration_bits (a b : ℕ) (j : Fin (2^b)) (x : Fin (2^a)) :
    (positionsEquiv (a+b)).symm (columnEnumeration a b ⟨j,x⟩) =
      Fin.append ((positionsEquiv a).symm x) ((positionsEquiv b).symm j) := by
  simp [columnEnumeration, sweepBoard, splitBinary]

lemma rowEnumeration_bits (a b : ℕ) (i : Fin (2^a)) (x : Fin (2^b)) :
    (positionsEquiv (a+b)).symm (rowEnumeration a b ⟨i,x⟩) =
      Fin.append ((positionsEquiv a).symm i) ((positionsEquiv b).symm x) := by
  simp [rowEnumeration, sweepBoard, splitBinary]

lemma coordinateSubgroup_iff (d : ℕ) (i : Fin d) (g : SymmetricGroup (2^d)) :
    g ∈ coordinateSubgroup d i ↔ ∀ x j, j ≠ i →
      (positionsEquiv d).symm (g x) j = (positionsEquiv d).symm x j := by
  constructor
  · intro hg x j hj
    exact coordinateSubgroup_bit ⟨g,hg⟩ x j hj
  · intro h x
    funext j
    exact h x j.1 j.2

lemma column_block_coordinate (a b : ℕ) (i : Fin a)
    (g : ∀ _ : Fin (2^b), SymmetricGroup (2^a)) :
    blockPermutation (columnEnumeration a b) g ∈ coordinateSubgroup (a+b) (i.castAdd b) ↔
      ∀ j, g j ∈ coordinateSubgroup a i := by
  simp only [coordinateSubgroup_iff]
  constructor
  · intro hg j x t ht
    have hh := hg (columnEnumeration a b ⟨j,x⟩) (t.castAdd b)
      (fun he => ht (Fin.ext (congrArg (fun y : Fin (a+b) => y.val) he)))
    simpa only [blockPermutation_apply, columnEnumeration_bits, Fin.append_left] using hh
  · intro hg x t ht
    obtain ⟨⟨j,x⟩,rfl⟩ := (columnEnumeration a b).surjective x
    rw [blockPermutation_apply, columnEnumeration_bits, columnEnumeration_bits]
    revert ht
    refine Fin.addCases ?_ ?_ t
    · intro t ht
      simp only [Fin.append_left]
      apply hg j x t
      intro he
      exact ht (congrArg (Fin.castAdd b) he)
    · intro t ht
      simp only [Fin.append_right]

lemma row_block_coordinate (a b : ℕ) (i : Fin b)
    (g : ∀ _ : Fin (2^a), SymmetricGroup (2^b)) :
    blockPermutation (rowEnumeration a b) g ∈ coordinateSubgroup (a+b) (i.natAdd a) ↔
      ∀ j, g j ∈ coordinateSubgroup b i := by
  simp only [coordinateSubgroup_iff]
  constructor
  · intro hg j x t ht
    have hh := hg (rowEnumeration a b ⟨j,x⟩) (t.natAdd a)
      (fun he => ht (Fin.ext (by have hh := congrArg Fin.val he; simpa using hh)))
    simpa only [blockPermutation_apply, rowEnumeration_bits, Fin.append_right] using hh
  · intro hg x t ht
    obtain ⟨⟨j,x⟩,rfl⟩ := (rowEnumeration a b).surjective x
    rw [blockPermutation_apply, rowEnumeration_bits, rowEnumeration_bits]
    revert ht
    refine Fin.addCases ?_ ?_ t
    · intro t ht
      simp only [Fin.append_left]
    · intro t ht
      simp only [Fin.append_right]
      apply hg j x t
      intro he
      exact ht (congrArg (Fin.natAdd a) he)

lemma coordinate_column_image (a b : ℕ) (i : Fin a) (g : SymmetricGroup (2^(a+b))) :
    g ∈ coordinateSubgroup (a+b) (i.castAdd b) ↔
      ∃ h : Fin (2^b) → coordinateSubgroup a i,
        blockPermutation (columnEnumeration a b) (fun j => (h j).val) = g := by
  constructor
  · intro hg
    have hc := first_layer_le_columns a b i hg
    have hc' : g ∈ fiberSubgroup (fun x => ((columnEnumeration a b).symm x).1) := by
      simpa only [columnGroup, columnEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
        Equiv.coe_fn_symm_mk, Equiv.prodComm_symm, Equiv.prodComm_apply, Equiv.symm_symm, Prod.swap] using hc
    obtain ⟨h,rfl⟩ := blockPermutation_exists (columnEnumeration a b) g hc'
    exact ⟨fun j => ⟨h j,(column_block_coordinate a b i h).mp hg j⟩,rfl⟩
  · rintro ⟨h,rfl⟩
    exact (column_block_coordinate a b i _).mpr (fun j => (h j).2)

lemma coordinate_row_image (a b : ℕ) (i : Fin b) (g : SymmetricGroup (2^(a+b))) :
    g ∈ coordinateSubgroup (a+b) (i.natAdd a) ↔
      ∃ h : Fin (2^a) → coordinateSubgroup b i,
        blockPermutation (rowEnumeration a b) (fun j => (h j).val) = g := by
  constructor
  · intro hg
    have hc := last_layer_le_rows a b i hg
    have hc' : g ∈ fiberSubgroup (fun x => ((rowEnumeration a b).symm x).1) := by
      simpa only [rowGroup, rowEnumeration, Equiv.symm_trans_apply, Equiv.sigmaEquivProd,
        Equiv.coe_fn_symm_mk, Equiv.symm_symm] using hc
    obtain ⟨h,rfl⟩ := blockPermutation_exists (rowEnumeration a b) g hc'
    exact ⟨fun j => ⟨h j,(row_block_coordinate a b i h).mp hg j⟩,rfl⟩
  · rintro ⟨h,rfl⟩
    exact (row_block_coordinate a b i _).mpr (fun j => (h j).2)

lemma column_layer_coefficient (a b : ℕ) (i : Fin a) :
    subgroupAverageCoefficient (coordinateSubgroup (a+b) (i.castAdd b)) =
      coefficientPush (blockPermutation (columnEnumeration a b))
        (productCoefficient (fun _ => subgroupAverageCoefficient (coordinateSubgroup a i))) := by
  rw [product_subgroupAverage, coefficientPush_comp]
  apply subgroupAverageCoefficient_image
  · exact (blockPermutation_injective _).comp (piHom_injective _ (fun _ => Subtype.val_injective))
  · exact coordinate_column_image a b i

lemma row_layer_coefficient (a b : ℕ) (i : Fin b) :
    subgroupAverageCoefficient (coordinateSubgroup (a+b) (i.natAdd a)) =
      coefficientPush (blockPermutation (rowEnumeration a b))
        (productCoefficient (fun _ => subgroupAverageCoefficient (coordinateSubgroup b i))) := by
  rw [product_subgroupAverage, coefficientPush_comp]
  apply subgroupAverageCoefficient_image
  · exact (blockPermutation_injective _).comp (piHom_injective _ (fun _ => Subtype.val_injective))
  · exact coordinate_row_image a b i

end SignedSweeps
end

end OAI
