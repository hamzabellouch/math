import OAI.Analysis.ProductSpaces.GaussianBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uE

namespace IndependentProducts

instance exponentialLaw_probability : IsProbabilityMeasure exponentialLaw :=
  isProbabilityMeasure_expMeasure (by norm_num)

lemma exponentialLaw_density : exponentialLaw =
    (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) := by
  change volume.withDensity (exponentialPDF 1) = _
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rw [exponentialPDF_eq]
  by_cases hp : 0 < x
  · simp [hp.le, hp]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [not_le.mpr hn, hp]

lemma exponentialLaw_positive : ∀ᵐ x ∂exponentialLaw, 0 < x := by
  rw [exponentialLaw_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (self_mem_ae_restrict measurableSet_Ioi)

lemma integral_exponentialLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (∫ x, f x ∂exponentialLaw) = ∫ x in Ioi 0, Real.exp (-x) • f x := by
  rw [exponentialLaw_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma integrable_exponentialLaw_iff {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : Integrable f exponentialLaw ↔
      Integrable (fun x => Real.exp (-x) • f x) (volume.restrict (Ioi 0)) := by
  rw [exponentialLaw_density, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma exponentialLaw_integrable_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) exponentialLaw := by
  rw [integrable_exponentialLaw_iff]
  simpa only [IntegrableOn, add_sub_cancel_right, Real.rpow_natCast, smul_eq_mul]
    using Real.GammaIntegral_convergent (s := n + 1) (by positivity)

lemma exponentialLaw_pow_integral (n : ℕ) : (∫ x : ℝ, x ^ n ∂exponentialLaw) = n.factorial := by
  rw [integral_exponentialLaw]
  have h := Real.Gamma_eq_integral (s := n + 1) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  exact h.symm

lemma exponentialLaw_mean : (∫ x : ℝ, x ∂exponentialLaw) = 1 := by
  simpa using exponentialLaw_pow_integral 1

lemma exponentialLaw_second : (∫ x : ℝ, x ^ 2 ∂exponentialLaw) = 2 := by
  simpa using exponentialLaw_pow_integral 2

lemma exponentialLaw_memLp : MemLp (fun x : ℝ => x) 2 exponentialLaw :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (exponentialLaw_integrable_pow 2)

lemma integral_complex_exp_exponentialLaw (z : ℂ) (hz : z.re < 1) :
    (∫ x : ℝ, Complex.exp (z * x) ∂exponentialLaw) = 1 / (1 - z) := by
  rw [integral_exponentialLaw]
  have he : (fun x : ℝ => Real.exp (-x) • Complex.exp (z * x)) =
      (fun x : ℝ => Complex.exp ((z - 1) * x)) := by
    funext x
    rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hz) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  calc
    -1 / (z - 1) = 1 / -(z - 1) := by rw [div_neg, neg_div]
    _ = 1 / (1 - z) := by congr 1; ring

lemma exponentialLaw_laplace (q : ℝ) (hq : 0 ≤ q) :
    (∫ x : ℝ, Complex.exp (-((q : ℂ) * x)) ∂exponentialLaw) = 1 / (1 + q) := by
  have hz : (-(q : ℂ)).re < 1 := by simp only [Complex.neg_re, Complex.ofReal_re]; linarith
  simpa only [neg_mul, sub_neg_eq_add] using integral_complex_exp_exponentialLaw (-(q : ℂ)) hz

lemma exponentialLaw_charFun (q : ℝ) : charFun exponentialLaw q = 1 / (1 - (q : ℂ) * Complex.I) := by
  rw [charFun_apply_real]
  convert integral_complex_exp_exponentialLaw ((q : ℂ) * Complex.I) (by simp) using 1
  congr 1
  funext x
  congr 1
  ring

end IndependentProducts

end

end OAI
