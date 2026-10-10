import OAI.Probability.InvariantIsing.Fields.FieldAffineSecondDerivative

namespace OAI

/-! The finite covariance-coordinate differential used in the joint
height Hessian. The final coordinate is the scalar spatial field. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

abbrev FieldCovariate (n : ℕ) := (Fin n → ℝ) × ℝ

def fieldFiniteLinear {n : ℕ} (A : Fin n → ℝ) (b : ℝ) : FieldCovariate n →L[ℝ] ℝ :=
  (∑ i, A i • ((ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ))) +
    b • ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ

@[simp] lemma fieldFiniteLinear_apply {n : ℕ} (A : Fin n → ℝ) (b : ℝ)
    (p : FieldCovariate n) : fieldFiniteLinear A b p = (∑ i, A i * p.1 i) + b * p.2 := by
  simp [fieldFiniteLinear]

lemma norm_fieldFiniteLinear_le {n : ℕ} (A : Fin n → ℝ) (b : ℝ) :
    ‖fieldFiniteLinear A b‖ ≤ (∑ i, |A i|) + |b| := by
  classical
  have hproj (i : Fin n) :
      ‖(ContinuousLinearMap.proj (R := ℝ) i).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simpa using (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
  unfold fieldFiniteLinear
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hproj i) (abs_nonneg _)).trans_eq (mul_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ (Fin n → ℝ) ℝ)
      (abs_nonneg _)).trans_eq (mul_one _)

lemma measurable_fieldFiniteLinear {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {A : Fin n → Ω → ℝ} {b : Ω → ℝ} (hA : ∀ i, Measurable (A i)) (hb : Measurable b) :
    Measurable (fun p => fieldFiniteLinear (fun i => A i p) (b p)) := by
  classical
  unfold fieldFiniteLinear
  exact (Finset.measurable_sum _ (fun i _ => (hA i).smul measurable_const)).add
    (hb.smul measurable_const)

lemma integral_fieldFiniteLinear {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A : Fin n → Ω → ℝ} {b : Ω → ℝ}
    (hA : ∀ i, Integrable (A i) μ) (hb : Integrable b μ) :
    (∫ p, fieldFiniteLinear (fun i => A i p) (b p) ∂μ) =
      fieldFiniteLinear (fun i => ∫ p, A i p ∂μ) (∫ p, b p ∂μ) := by
  classical
  unfold fieldFiniteLinear
  rw [integral_add (integrable_finsetSum _ (fun i _ => (hA i).smul_const _))
    (hb.smul_const _), integral_finsetSum _ (fun i _ => (hA i).smul_const _)]
  simp only [integral_smul_const]

end InvariantIsing

end

end OAI
