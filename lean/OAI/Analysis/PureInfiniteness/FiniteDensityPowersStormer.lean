import OAI.Analysis.OperatorAlgebra.FiniteOperatorPredual
import OAI.Analysis.NuclearUltrapower.HilbertSchmidt

namespace OAI

/-! The finite-dimensional Powers–Størmer inequality with the error measured
in the actual operator-predual norm. This is the norm supplied by the
hypertrace separation argument. -/

noncomputable section
open scoped InnerProductSpace TensorProduct ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

def finiteOperatorTraceDensity (T : H →L[ℂ] H) : finiteOperatorPredual (H := H) :=
  ∑ i, finiteOperatorCoefficient (stdOrthonormalBasis ℂ H i)
    (T (stdOrthonormalBasis ℂ H i))

omit [CompleteSpace H] in
lemma finiteOperatorTraceDensity_apply (T S : H →L[ℂ] H) :
    (finiteOperatorTraceDensity T).val S =
      LinearMap.trace ℂ H ((S * T).toLinearMap) := by
  classical
  simp only [finiteOperatorTraceDensity, Submodule.coe_sum, finiteOperatorCoefficient]
  rw [sum_apply, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H)]
  rfl

lemma trace_abs_le_predual_norm (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    (LinearMap.trace ℂ H (CFC.abs T).toLinearMap).re ≤
      ‖finiteOperatorTraceDensity T‖ := by
  obtain ⟨j, _, _, hj, _, hnj⟩ := NuclearUltrapower.PositiveTrace.exists_sign_of_finite_spectrum
    hT (NuclearUltrapower.operator_finite_real_spectrum T)
  rw [← hj, ← finiteOperatorTraceDensity_apply]
  calc
    ((finiteOperatorTraceDensity T).val j).re ≤
        ‖(finiteOperatorTraceDensity T).val j‖ := Complex.re_le_norm _
    _ ≤ ‖(finiteOperatorTraceDensity T).val‖ * ‖j‖ :=
      (finiteOperatorTraceDensity T).val.le_opNorm j
    _ ≤ ‖finiteOperatorTraceDensity T‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hnj

/-- The square roots of two positive density matrices differ in squared
Hilbert–Schmidt norm by at most the norm of their difference as functionals. -/
theorem finite_density_root_predual_bound (h k : H →L[ℂ] H)
    (hh : 0 ≤ h) (hk : 0 ≤ k) :
    ‖NuclearUltrapower.finiteOperatorTensor (CFC.sqrt h) -
      NuclearUltrapower.finiteOperatorTensor (CFC.sqrt k)‖ ^ 2 ≤
      ‖finiteOperatorTraceDensity (h - k)‖ := by
  rw [← NuclearUltrapower.finiteOperatorTensor_sub,
    NuclearUltrapower.finiteOperatorTensor_norm_sq,
    ((CFC.sqrt_nonneg h).isSelfAdjoint.sub (CFC.sqrt_nonneg k).isSelfAdjoint).star_eq]
  have hp := (NuclearUltrapower.operatorPositiveTrace (K := H)).powers_stormer_finite_spectrum
    (CFC.sqrt_nonneg h) (CFC.sqrt_nonneg k)
    (NuclearUltrapower.operator_finite_real_spectrum _)
  rw [CFC.sqrt_mul_sqrt_self h hh, CFC.sqrt_mul_sqrt_self k hk] at hp
  exact hp.trans (trace_abs_le_predual_norm (h - k) (hh.isSelfAdjoint.sub hk.isSelfAdjoint))

end WeakPureInfiniteness

end

end OAI
