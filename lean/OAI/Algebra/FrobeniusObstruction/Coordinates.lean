import Mathlib
import OAI.Algebra.FrobeniusObstruction.FrobeniusRing

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
open scoped TensorProduct
variable {ι κ k : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [CommRing k]
variable (ell : ℕ)

noncomputable def includeVariables (f : ι → κ) :
    Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := κ) (k := k) ell :=
  eval ell (fun i => coordinate ell (f i)) (fun i => coordinate_pow ell (f i))

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem includeVariables_coordinate (f : ι → κ) (i : ι) :
    includeVariables (k := k) ell f (coordinate ell i) = coordinate ell (f i) :=
  eval_coordinate _ _ _ _

noncomputable def merge :
    Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell →ₐ[k]
      Ring (ι := ι ⊕ κ) (k := k) ell :=
  Algebra.TensorProduct.lift (includeVariables ell Sum.inl) (includeVariables ell Sum.inr)
    (fun _ _ => Commute.all _ _)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem merge_tmul (a : Ring (ι := ι) (k := k) ell)
    (b : Ring (ι := κ) (k := k) ell) : merge (k := k) (ι := ι) (κ := κ) ell (a ⊗ₜ[k] b) =
      includeVariables (k := k) ell (Sum.inl : ι → ι ⊕ κ) a * includeVariables (k := k) ell (Sum.inr : κ → ι ⊕ κ) b := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ a b

noncomputable def splitCoordinates : ι ⊕ κ →
    Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell
  | .inl i => (Algebra.TensorProduct.includeLeft : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell) (coordinate ell i)
  | .inr j => (Algebra.TensorProduct.includeRight : Ring (ι := κ) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell) (coordinate ell j)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem splitCoordinates_pow (i : ι ⊕ κ) :
    splitCoordinates (k := k) ell i ^ ell = 0 := by
  cases i with
  | inl i => change ((Algebra.TensorProduct.includeLeft : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell) (coordinate ell i))^ell = 0
             rw [← map_pow, coordinate_pow, map_zero]
  | inr j => change ((Algebra.TensorProduct.includeRight : Ring (ι := κ) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell) (coordinate ell j))^ell = 0
             rw [← map_pow, coordinate_pow, map_zero]

noncomputable def splitBlocks : Ring (ι := ι ⊕ κ) (k := k) ell →ₐ[k]
    Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell :=
  eval ell (splitCoordinates (k := k) (ι := ι) (κ := κ) ell) (splitCoordinates_pow ell)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem split_coordinate (i : ι ⊕ κ) :
    splitBlocks (k := k) ell (coordinate ell i) = splitCoordinates ell i :=
  eval_coordinate _ _ _ _

omit [DecidableEq κ] in
@[simp] theorem split_includeVariables_left :
    (splitBlocks (k := k) (ι := ι) (κ := κ) ell).comp (includeVariables ell Sum.inl) =
      Algebra.TensorProduct.includeLeft := by
  refine algHom_ext (ι := ι) (k := k) (S := Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell) ell _ _ ?_
  intro i
  simp only [AlgHom.comp_apply, includeVariables_coordinate, split_coordinate]
  rfl

omit [DecidableEq ι] in
@[simp] theorem split_includeVariables_right :
    (splitBlocks (k := k) (ι := ι) (κ := κ) ell).comp (includeVariables ell Sum.inr) =
      Algebra.TensorProduct.includeRight := by
  refine algHom_ext (ι := κ) (k := k) (S := Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell) ell _ _ ?_
  intro i
  simp only [AlgHom.comp_apply, includeVariables_coordinate, split_coordinate]
  rfl

theorem merge_split :
    (merge (k := k) (ι := ι) (κ := κ) ell).comp (splitBlocks ell) = AlgHom.id k _ := by
  refine algHom_ext (ι := ι ⊕ κ) (k := k) (S := Ring (ι := ι ⊕ κ) (k := k) ell) ell _ _ ?_
  intro i
  cases i with
  | inl i => simp [splitCoordinates, Algebra.TensorProduct.includeLeft_apply]
  | inr j => simp [splitCoordinates, Algebra.TensorProduct.includeRight_apply]

theorem split_merge :
    (splitBlocks (k := k) (ι := ι) (κ := κ) ell).comp (merge (k := k) (ι := ι) (κ := κ) ell) = AlgHom.id k _ := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
      change splitBlocks (k := k) (ι := ι) (κ := κ) ell (merge (k := k) (ι := ι) (κ := κ) ell (a ⊗ₜ[k] b)) = a ⊗ₜ[k] b
      rw [merge_tmul, map_mul]
      have h1 := AlgHom.congr_fun (split_includeVariables_left (k := k) (ι := ι) (κ := κ) ell) a
      have h2 := AlgHom.congr_fun (split_includeVariables_right (k := k) (ι := ι) (κ := κ) ell) b
      rw [AlgHom.comp_apply] at h1 h2
      rw [h1, h2]
      simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

noncomputable def sumEquiv : Ring (ι := ι ⊕ κ) (k := k) ell ≃ₐ[k]
    Ring (ι := ι) (k := k) ell ⊗[k] Ring (ι := κ) (k := k) ell :=
  AlgEquiv.ofAlgHom (splitBlocks ell) (merge (k := k) (ι := ι) (κ := κ) ell) (split_merge ell) (merge_split (k := k) (ι := ι) (κ := κ) ell)

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
