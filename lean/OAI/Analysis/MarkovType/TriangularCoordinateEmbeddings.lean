import OAI.Analysis.MarkovType.TriangularCompletion
import OAI.Analysis.MarkovType.FiniteNormApproximation
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

private theorem realize_ofArray_bound (s : ∀ n : ℕ, TriangularSystem X n θ)
    (n : ℕ) {m : ℕ} (a : Fin m → ℝ) :
    ‖realize s n (C00.ofArray a)‖ ≤ ∑ i, |a i| := by
  classical
  change ‖realize s n (∑ i, Finsupp.single i.val (a i))‖ ≤ _
  rw [map_sum]
  apply norm_sum_le_of_le
  intro i hi
  rw [realize, Finsupp.linearCombination_single, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (vectorAt_bound s n i.val) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem coordinate_embeddings (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ)
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
      limitNorm s (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + η) * limitNorm s (C00.ofArray a) := by
  classical
  let C := NormedC00.coefficients (limitNorm s) (definite s hθ)
  let F : (Fin m → ℝ) →ₗ[ℝ] PreSpace s hθ := C.symm.toLinearMap.comp (C00.arrayLinear m)
  let E : Submodule ℝ (PreSpace s hθ) := LinearMap.range F
  let : FiniteDimensional ℝ E := LinearMap.finiteDimensional_range F
  let read : E →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x i => C (x : PreSpace s hθ) i.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let readL : E →L[ℝ] (Fin m → ℝ) := ⟨read, read.continuous_of_finiteDimensional⟩
  let A : ℕ → E →ₗ[ℝ] X := fun n =>
    (realize s n).comp (C.toLinearMap.comp E.subtype)
  let K : ℝ := (m : ℝ) * ‖readL‖
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg readL)
  have hbound (n : ℕ) (x : E) : ‖A n x‖ ≤ K * ‖x‖ := by
    obtain ⟨a, ha⟩ := x.property
    have hc : C (x : PreSpace s hθ) = C00.ofArray a := by
      rw [← ha]
      rfl
    have hr : readL x = a := by
      funext i
      change C (x : PreSpace s hθ) i.val = a i
      rw [hc]
      exact C00.ofArray_apply a i
    calc
      ‖A n x‖ = ‖realize s n (C00.ofArray a)‖ := by
        change ‖realize s n (C (x : PreSpace s hθ))‖ = _
        rw [hc]
      _ ≤ ∑ i, |a i| := realize_ofArray_bound s n a
      _ ≤ ∑ _i : Fin m, ‖readL x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hr, ← Real.norm_eq_abs]
        exact norm_le_pi_norm a i
      _ = (m : ℝ) * ‖readL x‖ := by simp
      _ ≤ (m : ℝ) * (‖readL‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (readL.le_opNorm x) (Nat.cast_nonneg m)
      _ = K * ‖x‖ := (mul_assoc _ _ _).symm
  have hlim (x : E) :
      Tendsto (fun n => ‖A n x‖) (freeUltrafilter : Filter ℕ) (𝓝 ‖x‖) := by
    exact tendsto_realULim freeUltrafilter (bounded s (C (x : PreSpace s hθ)))
  obtain ⟨S, hS⟩ := exists_near_isometric_map_of_pointwise
    (freeUltrafilter : Filter ℕ) A K hK hbound hlim hη
  refine ⟨S.comp F.rangeRestrict, ?_⟩
  intro a
  have hnorm : ‖F.rangeRestrict a‖ = limitNorm s (C00.ofArray a) := rfl
  simpa only [LinearMap.comp_apply, hnorm] using hS (F.rangeRestrict a)

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
