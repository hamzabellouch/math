import OAI.Probability.Renewal.Centered
import OAI.Probability.Renewal.GaussianCore

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

def localIntegrand (p : PMF ℕ) (k m : ℕ) (σ t : ℝ) : ℂ :=
  charFun (centeredMeasure p) (t / σ) ^ k *
    Complex.exp (-(((m : ℝ) - k * natMean p) / σ * t : ℝ) * Complex.I)

lemma localIntegrand_eq (p : PMF ℕ) (k m : ℕ) (σ t : ℝ) :
    localIntegrand p k m σ t = latticeChar p (t / σ) ^ k *
      Complex.exp (-((m : ℝ) * (t / σ) : ℝ) * Complex.I) := by
  rw [localIntegrand, centered_char, mul_pow, ← Complex.exp_nat_mul]
  have hid : ((k : ℂ) * (-((natMean p * (t / σ) : ℝ) : ℂ) * Complex.I)) +
      (-(((m : ℝ) - k * natMean p) / σ * t : ℝ) * Complex.I) =
        -((m : ℝ) * (t / σ) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add, hid]

lemma continuous_localIntegrand (p : PMF ℕ) (k m : ℕ) (σ : ℝ) :
    Continuous (localIntegrand p k m σ) := by
  unfold localIntegrand
  fun_prop

lemma norm_localIntegrand (p : PMF ℕ) (k m : ℕ) (σ t : ℝ) :
    ‖localIntegrand p k m σ t‖ = ‖latticeChar p (t / σ)‖ ^ k := by
  rw [localIntegrand_eq, norm_mul, norm_pow]
  simp only [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma scaled_inversion (p : PMF ℕ) (k m : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ in Icc (-Real.pi * σ) (Real.pi * σ), localIntegrand p k m σ t) =
      (2 * Real.pi * σ : ℂ) * ((sumLaw p k m).toReal : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by nlinarith [Real.pi_pos] : -Real.pi * σ ≤ Real.pi * σ)]
  simp_rw [localIntegrand_eq]
  rw [intervalIntegral.integral_comp_div (fun t => latticeChar p t ^ k *
    Complex.exp (-((m : ℝ) * t : ℝ) * Complex.I)) hσ.ne']
  simp only [mul_div_cancel_right₀ _ hσ.ne', sumLaw_inversion, Complex.real_smul]
  ring

def gaussianIntegrand (b t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) ^ 2 / 2)) * Complex.exp (-((b * t : ℝ) : ℂ) * Complex.I)

lemma continuous_gaussianIntegrand (b : ℝ) : Continuous (gaussianIntegrand b) := by
  unfold gaussianIntegrand
  fun_prop

lemma gaussianIntegrand_re (b t : ℝ) :
    (gaussianIntegrand b t).re = Real.exp (-t ^ 2 / 2) * Real.cos (b * t) := by
  have hid : -((t : ℂ) ^ 2 / 2) = ((-t ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [gaussianIntegrand, hid, ← Complex.ofReal_exp]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp [Complex.exp_re, Real.cos_neg]

lemma gaussian_core_lower {ω b : ℝ} (hω : 1 ≤ ω) (hb : |b| * ω ≤ 1) :
    Real.exp (-1) ≤ (∫ t : ℝ in Icc (-ω) ω, gaussianIntegrand b t).re := by
  have hω0 : 0 < ω := lt_of_lt_of_le zero_lt_one hω
  have hcos {t : ℝ} (ht : t ∈ Icc (-ω) ω) : (1 : ℝ) / 2 ≤ Real.cos (b * t) := by
    have habs : |b * t| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr ht) (abs_nonneg b)).trans hb
    have hsq : (b * t) ^ 2 ≤ 1 := by nlinarith [sq_abs (b * t), abs_nonneg (b * t)]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := b * t)]
  have hcont : Continuous (fun t => (gaussianIntegrand b t).re) := Complex.continuous_re.comp (continuous_gaussianIntegrand b)
  change Real.exp (-1) ≤ RCLike.re (∫ t : ℝ in Icc (-ω) ω, gaussianIntegrand b t)
  rw [← integral_re (continuous_gaussianIntegrand b).integrableOn_Icc]
  calc
    Real.exp (-1) = ∫ _ : ℝ in Icc (-1) 1, Real.exp (-1) / 2 := by norm_num; ring
    _ ≤ ∫ t : ℝ in Icc (-1) 1, (gaussianIntegrand b t).re := by
      apply setIntegral_mono_on (integrable_const _) hcont.integrableOn_Icc measurableSet_Icc
      intro t ht
      have htω : t ∈ Icc (-ω) ω := ⟨by linarith [ht.1], ht.2.trans hω⟩
      rw [gaussianIntegrand_re]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have hexp : Real.exp (-1) ≤ Real.exp (-t ^ 2 / 2) := Real.exp_le_exp.mpr (by linarith)
      have hh := mul_le_mul hexp (hcos htω) (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.exp_pos _).le
      nlinarith
    _ ≤ ∫ t : ℝ in Icc (-ω) ω, (gaussianIntegrand b t).re := by
      apply setIntegral_mono_set hcont.integrableOn_Icc
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [gaussianIntegrand_re]
        exact mul_nonneg (Real.exp_pos _).le (by linarith [hcos ht])
      · exact ae_of_all _ (fun t ht => ⟨by linarith [ht.1], ht.2.trans hω⟩)

lemma local_core_error (p : PMF ℕ)
    (h3 : Integrable (fun j : ℕ => (j : ℝ) ^ 3) p.toMeasure)
    {k : ℕ} (hk : 0 < k) (m : ℕ) {σ ω : ℝ} (hσ : 0 < σ) (hω : 0 ≤ ω)
    (hvar : σ ^ 2 = k * natVariance p) (hsmall : ω ^ 2 ≤ 2 * k) :
    ‖(∫ t : ℝ in Icc (-ω) ω, localIntegrand p k m σ t) -
      (∫ t : ℝ in Icc (-ω) ω, gaussianIntegrand (((m : ℝ) - k * natMean p) / σ) t)‖ ≤
      2 * ω * ((k * natThird p / σ ^ 3) * ω ^ 3 / 2 + ω ^ 4 / (4 * k)) := by
  have h1 : Integrable (fun j : ℕ => (j : ℝ)) p.toMeasure := by
    have hh := (nat_memLp p (by norm_num : (3 : ℕ) ≠ 0) h3).mono_exponent (by norm_num : (1 : ENNReal) ≤ 3)
    simpa using hh.integrable
  rw [← integral_sub (continuous_localIntegrand p k m σ).integrableOn_Icc
    (continuous_gaussianIntegrand _).integrableOn_Icc]
  have hh := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-ω) ω)
    (f := fun t => localIntegrand p k m σ t - gaussianIntegrand (((m : ℝ) - k * natMean p) / σ) t)
    (C := (k * natThird p / σ ^ 3) * ω ^ 3 / 2 + ω ^ 4 / (4 * k)) (by simp) (fun t ht => ?_)
  · rw [Real.volume_real_Icc] at hh
    simp only [sub_neg_eq_add, max_eq_left (by linarith : 0 ≤ ω + ω)] at hh
    exact hh.trans_eq (by ring)
  · have ht2 : t ^ 2 ≤ ω ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 0 ≤ ω + t)]
    have h := normalized_gaussian_power_error (centered_memLp p (by norm_num) h3)
      (centered_mean p h1) hk hσ (by simpa only [centered_variance] using hvar) t (ht2.trans hsmall)
    rw [centered_third] at h
    dsimp only [localIntegrand, gaussianIntegrand]
    rw [← sub_mul, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]
    refine h.trans ?_
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) 3)
        (by positivity [natThird_nonneg p])
    · apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr ht2) (by positivity : 0 ≤ ω ^ 2 + t ^ 2)]

lemma fourier_tail_bound {f : ℝ → ℂ} (hf : Continuous f) {g : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) {R ω η : ℝ} (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hbound : ∀ t ∈ Icc (-R) R, ‖f t‖ ≤ g t + η) :
    ‖∫ t : ℝ in Icc (-R) R \ Icc (-ω) ω, f t‖ ≤
      (∫ t : ℝ in (Icc (-ω) ω)ᶜ, g t) + 2 * R * η := by
  let s := Icc (-R) R \ Icc (-ω) ω
  have hfi : IntegrableOn f s := hf.integrableOn_Icc.mono_set sdiff_subset
  have hci : IntegrableOn (fun _ : ℝ => η) s :=
    (integrableOn_const (C := η) (s := Icc (-R) R) (by simp)).mono_set sdiff_subset
  calc
    ‖∫ t in s, f t‖ ≤ ∫ t in s, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in s, g t + η := by
      apply setIntegral_mono_on hfi.norm (hg.integrableOn.add hci) (measurableSet_Icc.diff measurableSet_Icc)
      exact fun t ht => hbound t ht.1
    _ = (∫ t in s, g t) + ∫ _ in s, η := integral_add hg.integrableOn hci
    _ ≤ (∫ t in (Icc (-ω) ω)ᶜ, g t) + ∫ _ : ℝ in Icc (-R) R, η := by
      apply add_le_add
      · apply setIntegral_mono_set hg.integrableOn (ae_of_all _ hg0)
        exact ae_of_all _ (fun _ ht => ht.2)
      · apply setIntegral_mono_set (integrable_const _) (ae_of_all _ (fun _ => hη))
        exact ae_of_all _ (fun _ ht => ht.1)
    _ = _ := by
      simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, Real.volume_real_Icc]
      rw [max_eq_left (by linarith : 0 ≤ R - -R)]
      ring

lemma local_lower_of_envelope (p : PMF ℕ)
    (h3 : Integrable (fun j : ℕ => (j : ℝ) ^ 3) p.toMeasure)
    {k : ℕ} (hk : 0 < k) (m : ℕ) {σ ω η : ℝ} (hσ : 0 < σ) (hω : 1 ≤ ω)
    (hvar : σ ^ 2 = k * natVariance p) (hsmall : ω ^ 2 ≤ 2 * k)
    (hwidth : ω ≤ Real.pi * σ)
    (hcenter : |((m : ℝ) - k * natMean p) / σ| * ω ≤ 1)
    {g : ℝ → ℝ} (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) (hη : 0 ≤ η)
    (hbound : ∀ t ∈ Icc (-Real.pi * σ) (Real.pi * σ),
      ‖latticeChar p (t / σ)‖ ^ k ≤ g t + η)
    (htail : (∫ t : ℝ in (Icc (-ω) ω)ᶜ, g t) ≤ Real.exp (-1) / 4)
    (hhigh : 2 * (Real.pi * σ) * η ≤ Real.exp (-1) / 4)
    (herror : 2 * ω * ((k * natThird p / σ ^ 3) * ω ^ 3 / 2 + ω ^ 4 / (4 * k)) ≤
      Real.exp (-1) / 4) :
    Real.exp (-1) / (8 * Real.pi * σ) ≤ (sumLaw p k m).toReal := by
  have hω0 : 0 ≤ ω := zero_le_one.trans hω
  have hR : 0 ≤ Real.pi * σ := by positivity
  have hsub : Icc (-ω) ω ⊆ Icc (-Real.pi * σ) (Real.pi * σ) :=
    fun _ ht => ⟨by linarith [ht.1], ht.2.trans hwidth⟩
  have he := (local_core_error p h3 hk m hσ hω0 hvar hsmall).trans herror
  have hc := gaussian_core_lower hω hcenter
  have ht := fourier_tail_bound (ω := ω) (continuous_localIntegrand p k m σ) hg hg0 hR hη (by
    intro t ht
    rw [norm_localIntegrand]
    exact hbound t (by simpa [neg_mul] using ht))
  have htail' : ‖∫ t : ℝ in Icc (-Real.pi * σ) (Real.pi * σ) \ Icc (-ω) ω,
      localIntegrand p k m σ t‖ ≤ Real.exp (-1) / 2 := by
    have hh := ht.trans (add_le_add htail hhigh)
    simp only [← neg_mul] at hh
    linarith
  have hdiff := Complex.re_le_norm ((∫ t : ℝ in Icc (-ω) ω, gaussianIntegrand
    (((m : ℝ) - k * natMean p) / σ) t) - ∫ t : ℝ in Icc (-ω) ω, localIntegrand p k m σ t)
  rw [norm_sub_rev, Complex.sub_re] at hdiff
  have hl := (abs_le.mp (Complex.abs_re_le_norm (∫ t : ℝ in Icc (-Real.pi * σ) (Real.pi * σ) \ Icc (-ω) ω,
    localIntegrand p k m σ t))).1
  have hlower : -Real.exp (-1) / 2 ≤
      (∫ t : ℝ in Icc (-Real.pi * σ) (Real.pi * σ) \ Icc (-ω) ω,
        localIntegrand p k m σ t).re := by linarith
  rw [setIntegral_sdiff measurableSet_Icc (continuous_localIntegrand p k m σ).integrableOn_Icc hsub,
    Complex.sub_re, scaled_inversion p k m hσ] at hlower
  norm_num [Complex.mul_re] at hlower
  apply (div_le_iff₀ (by positivity : 0 < 8 * Real.pi * σ)).mpr
  nlinarith

end HoneycombLocal

end

end OAI
