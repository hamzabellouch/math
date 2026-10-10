import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # A surjective differential has a fixed nonzero column minor -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

theorem exists_nonsingular_column_minor {n m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hA : Function.Surjective A) :
    ∃ j : Fin n → Fin m, Function.Injective j ∧
      (Matrix.of fun i k => A (Pi.single (j k) 1) i).det ≠ 0 := by
  classical
  let v : Fin m → (Fin n → ℝ) := fun i => A (Pi.single i 1)
  have hspan : ⊤ ≤ Submodule.span ℝ (range v) := by
    intro y _
    obtain ⟨x, rfl⟩ := hA y
    rw [pi_eq_sum_univ' x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  let J := (linearIndepOn_empty ℝ (id : (Fin n → ℝ) → (Fin n → ℝ))).extend (empty_subset (range v))
  let b : Basis J ℝ (Fin n → ℝ) := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using (finrank_eq_card_basis b).symm)
  let b' := b.reindex e
  have hb (k : Fin n) : ∃ i, v i = b' k := by
    simpa only [b', Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ range b from ⟨_, rfl⟩))
  choose j hj using hb
  refine ⟨j, ?_, ?_⟩
  · intro x y hxy
    apply b'.injective
    rw [← hj x, ← hj y, hxy]
  · have he : (Matrix.of fun i k => A (Pi.single (j k) 1) i) =
        LinearMap.toMatrix' b'.equivFun.symm.toLinearMap := by
      ext i k
      rw [LinearMap.toMatrix'_apply]
      change A (Pi.single (j k) 1) i = b'.equivFun.symm (Pi.single k 1) i
      have hs : b'.equivFun.symm (Pi.single k 1) = b' k := by
        apply b'.equivFun.injective
        simp
      rw [hs]
      exact congrFun (hj k) i
    rw [he, LinearMap.det_toMatrix']
    exact b'.equivFun.symm.isUnit_det'.ne_zero

end PolycyclicRecognition

end

end OAI
