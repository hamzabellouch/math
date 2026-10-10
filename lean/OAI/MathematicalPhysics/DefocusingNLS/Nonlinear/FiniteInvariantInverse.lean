import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # An inverse preserves every finite-dimensional invariant subspace -/

namespace DefocusingNLS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def HasContractingCoordinateInverse {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (π : H →L[ℝ] F) (S : H →L[ℝ] H) : Prop :=
  ∃ D R : π.range →L[ℝ] π.range,
    (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
    (∀ u, π.rangeRestrict (S u) = D (π.rangeRestrict u))

theorem finite_subspace_inverse_invariant (V : Submodule ℝ F) [FiniteDimensional ℝ V]
    (D R : F →L[ℝ] F) (hRD : ∀ v, R (D v) = v) (_hDR : ∀ v, D (R v) = v)
    (hD : ∀ v ∈ V, D v ∈ V) : ∀ v ∈ V, R v ∈ V := by
  let DV : V →L[ℝ] V := D.restrict hD
  have hDi : Function.Injective D := Function.LeftInverse.injective hRD
  have hi : Function.Injective DV := by
    intro u v huv
    apply Subtype.ext
    exact hDi (congrArg Subtype.val huv)
  have hs : Function.Surjective DV := LinearMap.injective_iff_surjective.mp hi
  intro v hv
  obtain ⟨u, hu⟩ := hs ⟨v, hv⟩
  have he : D (u : F) = v := congrArg Subtype.val hu
  have hr : R v = (u : F) := by rw [← he, hRD]
  rw [hr]
  exact u.property

theorem finite_subspace_contracting_inverse (V : Submodule ℝ F) [FiniteDimensional ℝ V]
    (D R : F →L[ℝ] F) (hRD : ∀ v, R (D v) = v) (hDR : ∀ v, D (R v) = v)
    (hD : ∀ v ∈ V, D v ∈ V) (hR : ‖R‖ ≤ 1) :
    ∃ Dv Rv : V →L[ℝ] V,
      (∀ v : V, (Dv v : F) = D v) ∧
      (∀ v : V, (Rv v : F) = R v) ∧
      (∀ v, Dv (Rv v) = v) ∧ ‖Rv‖ ≤ 1 := by
  have hi := finite_subspace_inverse_invariant V D R hRD hDR hD
  refine ⟨D.restrict hD, R.restrict hi, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro v
    exact Subtype.ext (hDR v)
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    exact (R.le_opNorm v).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg (v : F)))

end DefocusingNLS

end OAI
