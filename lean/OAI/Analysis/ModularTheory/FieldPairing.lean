import OAI.Analysis.OperatorAlgebra.ScalarKernelPairing
import OAI.Analysis.ModularTheory.KernelRegularization

namespace OAI

/-! The matrix coefficients of integrated modular fields, computed in the
actual noncommutative L² representation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularFieldOperator_pairing (S : BoundedRecovery.StandardModularData H)
    (a : ℝ → H →L[ℂ] H) (r : ℝ) (u v : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) :
    inner ℂ (modularFieldOperator S a r (scalarVectorLp volume u x))
      (scalarVectorLp volume v y) =
      ∫ s : ℝ, star (u (s - r)) * v s * inner ℂ (S.sigma (-s) (a r) x) y := by
  change inner ℂ (modularLpRepresentation volume S.D (a r)
    (modularLpTranslate volume r (scalarVectorLp volume u x))) _ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modularLpRepresentation_ae volume S.D (a r)
      (modularLpTranslate volume r (scalarVectorLp volume u x)),
    modularLpTranslate_ae volume r (scalarVectorLp volume u x),
    (measurePreserving_sub_right volume r).quasiMeasurePreserving.ae
      (scalarVectorLp_ae volume u x), scalarVectorLp_ae volume v y] with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  change _ = star (u (s - r)) * v s *
    inner ℂ (S.D.unitary (-s) (a r (S.D.unitary (-(-s)) x))) y
  rw [neg_neg]
  simp only [starRingEnd_apply]
  ring

lemma integratedModularField_pairing (S : BoundedRecovery.StandardModularData H)
    (a : ℝ → H →L[ℂ] H) (ha : Continuous a) (C : ℝ) (hC : ∀ r, ‖a r‖ ≤ C)
    (k : ℝ → ℂ) (hk : Integrable k)
    (u v : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) :
    inner ℂ (integratedModularField S a ha C hC k hk (scalarVectorLp volume u x))
      (scalarVectorLp volume v y) =
      ∫ r : ℝ, ∫ s : ℝ, star (k r) *
        (star (u (s - r)) * v s * inner ℂ (S.sigma (-s) (a r) x) y) := by
  have hi := BoundedRecovery.integrable_smul_bounded_orbit hk
    (modularFieldOperator_continuous S a ha (scalarVectorLp volume u x))
    (fun r => ((modularFieldOperator S a r).le_opNorm (scalarVectorLp volume u x)).trans
      (mul_le_mul_of_nonneg_right (modularFieldOperator_norm_le S a C hC r) (norm_nonneg _)))
  change inner ℂ (∫ r : ℝ, k r • modularFieldOperator S a r (scalarVectorLp volume u x)) _ = _
  refine (inner_integral_left hi (scalarVectorLp volume v y)).trans ?_
  apply integral_congr_ae
  filter_upwards [] with r
  rw [inner_smul_left, modularFieldOperator_pairing, ← integral_const_mul]
  rfl

lemma modularKernelRegularization_pairing (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : ∀ s f, T (modularRightTranslation volume S.D s f) =
      modularRightTranslation volume S.D s (T f))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ)) (k : ℝ → ℂ) (hk : Integrable k) (x y : H) :
    inner ℂ (modularKernelRegularization S T f g k hk (scalarVectorLp volume u x))
      (scalarVectorLp volume v y) =
      ∫ r : ℝ, ∫ s : ℝ, star (k r) *
        (star (u (s - r)) * v s * inner ℂ (modularSliceKernel T f g s (s - r) x) y) := by
  refine (integratedModularField_pairing S (modularKernelCoefficient T f g)
    (modularKernelCoefficient_continuous T f g) _ (modularKernelCoefficient_bound T f g)
    k hk u v x y).trans ?_
  apply integral_congr_ae
  filter_upwards [] with r
  apply integral_congr_ae
  filter_upwards [] with s
  have hc := modularSliceKernel_covariance S T hT f g s (s - r)
  rw [show s - r - s = -r by ring] at hc
  change star (k r) * (star (u (s - r)) * v s *
    inner ℂ (S.sigma (-s) (modularSliceKernel T f g 0 (-r)) x) y) = _
  rw [← hc]

end WeakPureInfiniteness

end

end OAI
