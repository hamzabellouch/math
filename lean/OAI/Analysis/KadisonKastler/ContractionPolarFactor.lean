import OAI.Analysis.KadisonKastler.HilbertDefect

namespace OAI

/-! # A contractive polar factor for a Hilbert-space operator

Only the factor and its adjoint identity are needed for finite coefficient
duality. There is no closed-range or finite-dimensional hypothesis here.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem contraction_adjoint_self_of_norm_eq (U : E →L[ℂ] F) (hU : ‖U‖ ≤ 1)
    (x : E) (hx : ‖U x‖ = ‖x‖) : U.adjoint (U x) = x := by
  have hd : operatorDefect U x = 0 := by
    apply norm_eq_zero.mp
    have h := norm_operatorDefect_sq U hU x
    rw [hx, sub_self] at h
    nlinarith [norm_nonneg (operatorDefect U x)]
  have h := congrArg (fun A : E →L[ℂ] E => A x) (operatorDefect_sq U hU)
  change operatorDefect U (operatorDefect U x) = x - U.adjoint (U x) at h
  rw [hd, map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The positive modulus has the same vector norms as the original operator. -/
theorem operator_modulus_norm (T : E →L[ℂ] F) (x : E) :
    ‖CFC.sqrt (T.adjoint.comp T) x‖ = ‖T x‖ := by
  let R := CFC.sqrt (T.adjoint.comp T)
  have hR : R.adjoint = R := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hsq : R.adjoint.comp R = T.adjoint.comp T := by
    rw [hR]
    exact CFC.sqrt_mul_sqrt_self _
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (ContinuousLinearMap.isPositive_adjoint_comp_self T))
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  change (inner ℂ x ((R.adjoint.comp R) x)).re = _
  rw [hsq]
  rfl

/-- A contractive polar factor suffices for the exact trace-norm duality.
The second identity records that its adjoint recovers the positive modulus. -/
theorem exists_contractive_polar_factor (T : E →L[ℂ] F) :
    ∃ U : E →L[ℂ] F, ‖U‖ ≤ 1 ∧
      U.comp (CFC.sqrt (T.adjoint.comp T)) = T ∧
      U.adjoint.comp T = CFC.sqrt (T.adjoint.comp T) := by
  let R := CFC.sqrt (T.adjoint.comp T)
  obtain ⟨U, hU, hUT⟩ := exists_contraction_factor R T
    (fun x => (operator_modulus_norm T x).ge)
  refine ⟨U, hU, hUT, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hx : U (R x) = T x := congrArg (fun S : E →L[ℂ] F => S x) hUT
  rw [ContinuousLinearMap.comp_apply, ← hx]
  apply contraction_adjoint_self_of_norm_eq U hU
  rw [hx]
  exact (operator_modulus_norm T x).symm

end

end KadisonKastler

end OAI
