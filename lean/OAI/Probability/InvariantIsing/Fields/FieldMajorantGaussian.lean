import OAI.Probability.InvariantIsing.Fields.FieldMajorant

namespace OAI

/-! The sharp one-step Gaussian estimate for the entropy-domain majorant. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

/-- Positive logarithmic means increase with their exponent. -/
lemma log_moment_div_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Ω → ℝ}
    (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t * F x)) μ)
    {a d : ℝ} (ha : 0 < a) (had : a ≤ d) :
    a⁻¹ * Real.log (∫ x, Real.exp (a * F x) ∂μ) ≤
      d⁻¹ * Real.log (∫ x, Real.exp (d * F x) ∂μ) := by
  have hd : 0 < d := ha.trans_le had
  have hc := (IsingPerceptron.convexOn_cgf_of_all_exp he).2
    (mem_univ (0 : ℝ)) (mem_univ d)
    (show 0 ≤ 1 - a / d by exact sub_nonneg.mpr ((div_le_one hd).2 had))
    (div_nonneg ha.le hd.le) (by ring : 1 - a / d + a / d = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, cgf_zero] at hc
  have hx : a / d * d = a := div_mul_cancel₀ _ hd.ne'
  rw [hx] at hc
  change Real.log (∫ x, Real.exp (a * F x) ∂μ) ≤
    a / d * Real.log (∫ x, Real.exp (d * F x) ∂μ) at hc
  calc
    _ ≤ a⁻¹ * (a / d * Real.log (∫ x, Real.exp (d * F x) ∂μ)) :=
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr ha.le)
    _ = _ := by field_simp

/-- Jensen at exponent zero, under the same actual moment assumptions. -/
lemma mean_le_log_moment_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hi : Integrable F μ)
    {d : ℝ} (hd : 0 < d) (he : Integrable (fun x => Real.exp (d * F x)) μ) :
    (∫ x, F x ∂μ) ≤ d⁻¹ * Real.log (∫ x, Real.exp (d * F x) ∂μ) := by
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun x => mem_univ (d * F x))) (hi.const_mul d) he
  have hl := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp, integral_const_mul] at hl
  have ht := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hd.le)
  have heq : d⁻¹ * (d * ∫ x, F x ∂μ) = ∫ x, F x ∂μ := by field_simp
  rwa [heq] at ht

lemma fieldMajorant_gaussian_moment_bound {d a v : ℝ} (hd : 0 < d) (hda : d ≤ a)
    (hv : 0 ≤ v) (z : ℝ) :
    (∫ y : ℝ, Real.exp (a * fieldMajorant d (z + Real.sqrt v * y))
      ∂gaussianReal 0 1) ≤ Real.exp (a * fieldMajorant d z + a ^ 2 * v / 2) := by
  let A := Real.exp (d * z) / (Real.exp (d * z) + Real.exp (-d * z))
  let B := Real.exp (-d * z) / (Real.exp (d * z) + Real.exp (-d * z))
  have hAB : A + B = 1 := by
    dsimp [A, B]
    rw [← add_div, div_self (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne']
  let R := fun y : ℝ => Real.exp (a * fieldMajorant d z) *
    (A * Real.exp ((a * Real.sqrt v) * y) + B * Real.exp ((-a * Real.sqrt v) * y))
  have hiR : Integrable R (gaussianReal 0 1) :=
    (((integrable_exp_mul_gaussianReal _).const_mul A).add
      ((integrable_exp_mul_gaussianReal _).const_mul B)).const_mul _
  have hp (y : ℝ) : Real.exp (a * fieldMajorant d (z + Real.sqrt v * y)) ≤ R y := by
    have h := mul_le_mul_of_nonneg_left
      (fieldMajorant_increment_exp_le hd hda z (Real.sqrt v * y))
      (Real.exp_pos (a * fieldMajorant d z)).le
    have he : Real.exp (a * fieldMajorant d z) *
        Real.exp (a * (fieldMajorant d (z + Real.sqrt v * y) - fieldMajorant d z)) =
        Real.exp (a * fieldMajorant d (z + Real.sqrt v * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at h
    simpa only [R, A, B, mul_assoc] using h
  calc
    _ ≤ ∫ y, R y ∂gaussianReal 0 1 :=
      integral_mono (integrable_exp_fieldMajorant hd _ _ _) hiR hp
    _ = _ := by
      rw [show R = fun y => Real.exp (a * fieldMajorant d z) *
        (A * Real.exp ((a * Real.sqrt v) * y) +
          B * Real.exp ((-a * Real.sqrt v) * y)) from rfl,
        integral_const_mul,
        integral_add ((integrable_exp_mul_gaussianReal _).const_mul A)
          ((integrable_exp_mul_gaussianReal _).const_mul B),
        integral_const_mul, integral_const_mul]
      have hmgf (t : ℝ) : (∫ y : ℝ, Real.exp (t * y) ∂gaussianReal 0 1) =
          Real.exp (t ^ 2 / 2) := by
        simpa [mgf] using mgf_gaussianReal (p := gaussianReal 0 1) (μ := 0) (v := 1)
          (X := fun y : ℝ => y) (by simp) t
      rw [hmgf, hmgf]
      have hsq : (a * Real.sqrt v) ^ 2 = a ^ 2 * v := by
        rw [mul_pow, Real.sq_sqrt hv]
      have hsq' : (-a * Real.sqrt v) ^ 2 = a ^ 2 * v := by
        rw [mul_pow, neg_sq, Real.sq_sqrt hv]
      rw [hsq, hsq', ← add_mul, hAB, one_mul, ← Real.exp_add]

lemma gaussianOperator_fieldMajorant_high {d a v : ℝ} (hd : 0 < d) (hda : d ≤ a)
    (hv : 0 ≤ v) (z : ℝ) :
    gaussianOperator a v (fieldMajorant d) z ≤ fieldMajorant d z + a * v / 2 := by
  have ha : 0 < a := hd.trans_le hda
  have hp := IsingPerceptron.integral_exp_pos (gaussianReal 0 1) _
    (integrable_exp_fieldMajorant hd z (Real.sqrt v) a)
  have hl := Real.log_le_log hp (fieldMajorant_gaussian_moment_bound hd hda hv z)
  rw [Real.log_exp] at hl
  simp only [gaussianOperator, ha.ne', ite_false]
  calc
    _ ≤ a⁻¹ * (a * fieldMajorant d z + a ^ 2 * v / 2) :=
      mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr ha.le)
    _ = _ := by field_simp

/-- The exact estimate (fld:majorant), including the zero-exponent root step. -/
lemma gaussianOperator_fieldMajorant {d a v : ℝ} (hd : 0 < d) (ha : 0 ≤ a)
    (hv : 0 ≤ v) (z : ℝ) :
    gaussianOperator a v (fieldMajorant d) z ≤
      fieldMajorant d z + max a d * v / 2 := by
  by_cases hda : d ≤ a
  · simpa only [max_eq_left hda] using gaussianOperator_fieldMajorant_high hd hda hv z
  have had : a ≤ d := (lt_of_not_ge hda).le
  have hcap := gaussianOperator_fieldMajorant_high hd le_rfl hv z
  rw [max_eq_right had]
  apply le_trans _ hcap
  by_cases ha0 : a = 0
  · simp only [gaussianOperator, ha0, ite_true, hd.ne', ite_false]
    exact mean_le_log_moment_div (gaussianReal 0 1)
      (IsingPerceptron.gaussian_linearGrowth_integrable
        ((measurable_fieldMajorant d).comp (measurable_const.add (measurable_id.const_mul _)))
        (((fieldMajorant_linearGrowth hd).add_left z).scale_argument (Real.sqrt v)) _ _)
      hd (integrable_exp_fieldMajorant hd _ _ _)
  · simp only [gaussianOperator, ha0, hd.ne', ite_false]
    exact log_moment_div_mono (gaussianReal 0 1)
      (fun t => integrable_exp_fieldMajorant hd z (Real.sqrt v) t)
      (lt_of_le_of_ne ha (Ne.symm ha0)) had

end InvariantIsing

end

end OAI
