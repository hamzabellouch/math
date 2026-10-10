import OAI.Analysis.KadisonKastler.ProbabilityOperatorAlgebra

namespace OAI

/-! # Integrable scalar weights on bounded operator fields

Vectorwise integration needs only strong measurability on each vector.
An integrable scalar weight therefore defines a bounded operator, and
commutation and von Neumann algebra membership pass to this operator.
This applies in particular to the compactly weighted convolution
operators in the regular representation.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_weighted_operator_vector
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (x : H) :
    Integrable (fun t => w t • F t x) μ := by
  apply (hw.norm.mul_const (C * ‖x‖)).mono'
    (hw.aestronglyMeasurable.smul (hm x))
  filter_upwards [hb] with t ht
  change ‖w t • F t x‖ ≤ ‖w t‖ * (C * ‖x‖)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (((F t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg x))) (norm_nonneg _)

omit [CompleteSpace H] in
private theorem norm_integral_weighted_operator_vector_le
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H) (C : ℝ)
    (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (x : H) :
    ‖∫ t, w t • F t x ∂μ‖ ≤ (∫ t, ‖w t‖ ∂μ) * C * ‖x‖ := by
  calc
    ‖∫ t, w t • F t x ∂μ‖ ≤ ∫ t, ‖w t‖ * (C * ‖x‖) ∂μ := by
      apply norm_integral_le_of_norm_le (hw.norm.mul_const (C * ‖x‖))
      filter_upwards [hb] with t ht
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (((F t).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right ht (norm_nonneg x))) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

/-- Integrating an integrably weighted, uniformly bounded field on vectors. -/
def weightedOperatorIntegral
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t, w t • F t x ∂μ
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_weighted_operator_vector μ w hw F hm C hb x)
          (integrable_weighted_operator_vector μ w hw F hm C hb y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (w _) c]
        exact integral_smul c (fun t => w t • F t x) }
    ((∫ t, ‖w t‖ ∂μ) * C)
    (norm_integral_weighted_operator_vector_le μ w hw F C hb)

omit [CompleteSpace H] in
@[simp] theorem weightedOperatorIntegral_apply
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (x : H) :
    weightedOperatorIntegral μ w hw F hm C hb x = ∫ t, w t • F t x ∂μ := rfl

omit [CompleteSpace H] in
theorem norm_weightedOperatorIntegral_le
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) :
    ‖weightedOperatorIntegral μ w hw F hm C hb‖ ≤ (∫ t, ‖w t‖ ∂μ) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hC)
  exact norm_integral_weighted_operator_vector_le μ w hw F C hb

theorem weightedOperatorIntegral_commutes
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (A : H →L[ℂ] H)
    (hA : ∀ᵐ t ∂μ, F t * A = A * F t) :
    weightedOperatorIntegral μ w hw F hm C hb * A =
      A * weightedOperatorIntegral μ w hw F hm C hb := by
  ext x
  change (∫ t, w t • F t (A x) ∂μ) = A (∫ t, w t • F t x ∂μ)
  rw [← A.integral_comp_comm (integrable_weighted_operator_vector μ w hw F hm C hb x)]
  apply integral_congr_ae
  filter_upwards [hA] with t ht
  rw [map_smul]
  exact congrArg (fun y : H => w t • y)
    (congrArg (fun B : H →L[ℂ] H => B x) ht)

/-- Membership is checked against the commutant, with no norm-topology
measurability assumption on the operator field. -/
theorem weightedOperatorIntegral_mem
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (M : VonNeumannAlgebra H)
    (hM : ∀ᵐ t ∂μ, F t ∈ M) :
    weightedOperatorIntegral μ w hw F hm C hb ∈ M := by
  change weightedOperatorIntegral μ w hw F hm C hb ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro A hA
  apply (weightedOperatorIntegral_commutes μ w hw F hm C hb A ?_).symm
  filter_upwards [hM] with t ht
  exact hA (F t) ht

end

end KadisonKastler

end OAI
