import Mathlib

namespace OAI

/-! Uniform signed stationary phase, oscillatory integral estimates, and summed coefficient-mass control. -/

noncomputable section

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
namespace ThreeTorus

lemma quadratic_gaussian_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hi : Integrable (fun x : ℝ => Complex.exp (-Real.pi * b * x ^ 2)) := by
    have hb' : 0 < ((Real.pi : ℂ) * b).re := by
      simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using mul_pos Real.pi_pos hb
    simpa only [neg_mul, mul_zero, zero_mul, add_zero] using
      integrable_cexp_quadratic hb' 0 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner (𝓕⁻ f).integrable hi
  have hinv : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = (f : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  have h' : (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      ∫ x : ℝ, (𝓕⁻ f) x * (𝓕 fun y : ℝ => Complex.exp (-Real.pi * b * y ^ 2)) x := by
    rw [flip_innerₗ] at h
    change (∫ x : ℝ, (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x •
      Complex.exp (-Real.pi * b * x ^ 2)) = _ at h
    simpa only [hinv, smul_eq_mul] using! h
  rw [h', fourier_gaussian_pi hb, ← integral_const_mul]
  congr 1
  ext x
  ring

lemma norm_quadratic_exp_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * b * x ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have he : (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2).re = -Real.pi * b.re * x ^ 2 := by
    simp [mul_re, mul_im, pow_two]
  rw [he]
  have := mul_nonneg (mul_nonneg Real.pi_pos.le hb) (sq_nonneg x)
  linarith

/-- The Gaussian identity extends to the imaginary boundary after pairing with
an integrable Schwartz amplitude. This uses dominated convergence, never a
non-absolutely convergent Bochner integral for a bare Fresnel kernel. -/
lemma quadratic_boundary_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ}
    (hb : 0 ≤ b.re) (hbslit : b ∈ Complex.slitPlane) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hb0 : b ≠ 0 := Complex.slitPlane_ne_zero hbslit
  have hparam : Tendsto (fun ε : ℝ => b + (ε : ℂ)) (𝓝[>] 0) (𝓝 b) := by
    have hcast : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using hcast.const_add b
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hre : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < (b + (ε : ℂ)).re := by
    filter_upwards [heps] with ε hε
    simp only [add_re, ofReal_re]
    linarith
  have hleft : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      f x * Complex.exp (-Real.pi * (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      ?_ ?_ f.integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hε.le x)
        (norm_nonneg (f x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((hparam.const_mul _).mul_const _).cexp)
  have hintegral : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (𝓕⁻ f) x * Complex.exp (-Real.pi / (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, (𝓕⁻ f) x * Complex.exp (-Real.pi / b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖(𝓕⁻ f) x‖)
      ?_ ?_ (𝓕⁻ f).integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul, div_eq_mul_inv]
      have hb' : 0 ≤ (b + (ε : ℂ))⁻¹.re := by
        rw [Complex.inv_re]
        exact div_nonneg hε.le (Complex.normSq_nonneg _)
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hb' x)
        (norm_nonneg ((𝓕⁻ f) x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((tendsto_const_nhds.div hparam hb0).mul_const _).cexp)
  have hpow : Tendsto (fun ε : ℝ => 1 / (b + (ε : ℂ)) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    apply tendsto_const_nhds.div
    · exact (continuousAt_cpow_const hbslit).tendsto.comp hparam
    · exact cpow_ne_zero_iff.mpr (Or.inl hb0)
  have hr := hpow.mul hintegral
  have hright := hr.congr' (hre.mono (fun ε hε => (quadratic_gaussian_pairing f hε).symm))
  exact tendsto_nhds_unique hleft hright

lemma cpow_pos_mul {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((t : ℂ) * z) ^ w = (t : ℂ) ^ w * z ^ w := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ht.ne') hz),
    Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul ht hz,
    ← Complex.ofReal_log ht.le, add_mul, Complex.exp_add]

lemma quadratic_factor {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) / ((t : ℂ) * (-I)) ^ (1 / 2 : ℂ) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) := by
  have hs : (Real.sqrt t : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  rw [cpow_pos_mul ht (neg_ne_zero.mpr I_ne_zero), hs, div_mul_eq_div_div,
    div_self (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))),
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I,
    one_div, ← Complex.exp_neg]
  congr 1
  ring

lemma integral_fourierInv (f : 𝓢(ℝ, ℂ)) : (∫ x : ℝ, (𝓕⁻ f) x) = f 0 := by
  have he : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) 0 = f 0 := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  simpa [Real.fourier_eq] using he

lemma quadratic_stationary_identity (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) *
        (∫ ξ : ℝ, (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
  have hb : 0 ≤ ((t : ℂ) * (-I)).re := by simp
  have hslit : (t : ℂ) * (-I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using ht.ne'
  have he := quadratic_boundary_pairing f hb hslit
  have hleft : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) * ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (Real.pi * t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    ring
  have hright : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) / ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (-Real.pi / t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    field_simp
    simp [I_sq]
    ring
  simp only [hleft, hright] at he
  rw [he, ← mul_assoc, ← div_eq_mul_one_div, quadratic_factor ht]

lemma quadratic_stationary_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    ‖(Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
      Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0‖ ≤
        (Real.pi / t) * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
  rw [quadratic_stationary_identity f ht, ← mul_sub, norm_mul]
  have hnorm : ‖Complex.exp ((Real.pi : ℂ) / 4 * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm, one_mul, ← integral_fourierInv f]
  have hi : Integrable (fun ξ : ℝ => (𝓕⁻ f) ξ *
      Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
    apply ((𝓕⁻ f).integrable (μ := volume)).mul_bdd
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards [] with ξ
      have he : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))‖ = 1 := by
        rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
      exact he.le
  rw [← integral_sub hi (𝓕⁻ f).integrable]
  have hd : Integrable (fun ξ : ℝ => ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
    have hh := (𝓕⁻ f).integrable_pow_mul volume 2
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hd.const_mul (Real.pi / t))
  filter_upwards [] with ξ
  have heq : (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - (𝓕⁻ f) ξ =
      (𝓕⁻ f) ξ * (Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1) := by ring
  rw [heq, norm_mul]
  have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -Real.pi / t * ξ^2)
  have he' : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
      Real.pi / t * ξ^2 := by
    convert he using 1
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos ht, abs_of_nonneg (sq_nonneg ξ)]
  calc
    ‖(𝓕⁻ f) ξ‖ * ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
        ‖(𝓕⁻ f) ξ‖ * (Real.pi / t * ξ^2) :=
      mul_le_mul_of_nonneg_left he' (norm_nonneg _)
    _ = _ := by ring

lemma quadratic_stationary_limit (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)) := by
  have hlim : Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
      (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact quadratic_stationary_error f ht
    · simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const
        (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖)
  simpa using hlim.add_const (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)

lemma quadratic_stationary_uniform {A : Type*} (f : A → 𝓢(ℝ, ℂ)) (M : ℝ)
    (hM : ∀ a, (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ (f a)) ξ‖) ≤ M) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f a x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))))
      (fun a => Complex.exp ((Real.pi : ℂ) / 4 * I) * f a 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun t : ℝ => (Real.pi / t) * M) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const M
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hε)] with t ht hεt
  intro a
  rw [dist_comm, dist_eq_norm]
  exact ((quadratic_stationary_error (f a) ht).trans
    (mul_le_mul_of_nonneg_left (hM a) (div_pos Real.pi_pos ht).le)).trans_lt hεt

lemma quadratic_stationary_compact {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)) :=
  quadratic_stationary_limit (hf.toSchwartzMap hsm)

lemma continuous_stationary_constant :
    Continuous (fun f : 𝓢(ℝ, ℂ) => ∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
  have hg : Function.HasTemperateGrowth (fun ξ : ℝ => ξ^2) := by fun_prop
  have he (f : 𝓢(ℝ, ℂ)) : (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖) =
      ‖((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => ξ^2)) (𝓕⁻ f)).toLp 1 volume‖ := by
    rw [SchwartzMap.norm_toLp_one]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [SchwartzMap.smulLeftCLM_apply hg, norm_smul]
    simp [Real.norm_eq_abs]
  simp_rw [he]
  fun_prop

lemma quadratic_stationary_uniform_compact {A : Type*} [TopologicalSpace A]
    [CompactSpace A] (f : A → 𝓢(ℝ, ℂ)) (hf : Continuous f) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f a x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))))
      (fun a => Complex.exp ((Real.pi : ℂ) / 4 * I) * f a 0) atTop := by
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image
    (continuous_stationary_constant.comp hf).continuousOn
  apply quadratic_stationary_uniform f M
  intro a
  apply hM
  exact ⟨a, mem_univ a, rfl⟩

lemma quadratic_stationary_limit_neg (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (-I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp (-(Real.pi : ℂ) / 4 * I) * f 0)) := by
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f
  have h := Complex.continuous_conj.continuousAt.tendsto.comp (quadratic_stationary_limit g)
  have hg (x : ℝ) : (starRingEnd ℂ) (g x) = f x := by
    simp [g, SchwartzMap.postcompCLM_apply]
  have he : (starRingEnd ℂ) (Complex.exp ((Real.pi : ℂ) / 4 * I)) =
      Complex.exp (-(Real.pi : ℂ) / 4 * I) := by
    rw [← Complex.exp_conj]
    congr 1
    have hm : (starRingEnd ℂ) (4 : ℂ) = 4 := by
      exact_mod_cast Complex.conj_ofReal (4 : ℝ)
    simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, hm]
    ring
  have hexp (r : ℝ) : (starRingEnd ℂ) (Complex.exp (I * (r : ℂ))) =
      Complex.exp (-I * (r : ℂ)) := by
    rw [← Complex.exp_conj]
    simp
  simpa only [Function.comp_def, map_mul, Complex.conj_ofReal, ← integral_conj,
    hg, he, hexp] using h

lemma quadratic_stationary_compact_neg {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (-I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp (-(Real.pi : ℂ) / 4 * I) * f 0)) :=
  quadratic_stationary_limit_neg (hf.toSchwartzMap hsm)

lemma oscillatory_integral_parts {a b t : ℝ} (ht : t ≠ 0)
    {φ φ' : ℝ → ℝ} {B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hB' : IntervalIntegrable B' volume a b) :
    (∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) =
      (1 / (I * (t : ℂ))) *
        (B b * Complex.exp (I * (t * φ b : ℝ)) -
          B a * Complex.exp (I * (t * φ a : ℝ)) -
            ∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))) := by
  have hv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun x => Complex.exp (I * (t * φ x : ℝ)))
        (Complex.exp (I * (t * φ x : ℝ)) * (I * (t * φ' x : ℝ))) x := by
    exact (((hφ x hx).const_mul t).ofReal_comp.const_mul I).cexp
  have hφc : ContinuousOn φ (uIcc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable
      (fun x => Complex.exp (I * (t * φ x : ℝ)) * (I * (t * φ' x : ℝ))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul hB hv hB' hvi
  have hj : (∫ x in a..b, B x * (Complex.exp (I * (t * φ x : ℝ)) *
      (I * (t * φ' x : ℝ)))) = (I * (t : ℂ)) *
        (∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    ring
  rw [hj] at he
  rw [← he]
  field_simp [ofReal_ne_zero.mpr ht]

lemma oscillatory_integral_bound {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0)
    {φ φ' : ℝ → ℝ} {B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hB' : IntervalIntegrable B' volume a b) :
    ‖∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (1 / |t|) * (‖B b‖ + ‖B a‖ + ∫ x in a..b, ‖B' x‖) := by
  rw [oscillatory_integral_parts ht hφ hB hφ' hB', norm_mul]
  have he (r : ℝ) : ‖Complex.exp (I * (r : ℂ))‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  have hc : ‖1 / (I * (t : ℂ))‖ = 1 / |t| := by simp
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖B b * Complex.exp (I * (t * φ b : ℝ)) -
      B a * Complex.exp (I * (t * φ a : ℝ)) -
        ∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      ‖B b * Complex.exp (I * (t * φ b : ℝ)) -
        B a * Complex.exp (I * (t * φ a : ℝ))‖ +
          ‖∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))‖ := norm_sub_le _ _
    _ ≤ (‖B b‖ + ‖B a‖) + ∫ x in a..b, ‖B' x‖ := by
      apply add_le_add
      · simpa only [norm_mul, he, mul_one] using
          norm_sub_le (B b * Complex.exp (I * (t * φ b : ℝ)))
            (B a * Complex.exp (I * (t * φ a : ℝ)))
      · simpa only [norm_mul, he, mul_one] using
          intervalIntegral.norm_integral_le_integral_norm hab
            (f := fun x => B' x * Complex.exp (I * (t * φ x : ℝ)))

lemma reciprocal_variation {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    {q q' : ℝ → ℝ}
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hqc : ContinuousOn q' (Icc a b))
    (hsep : ∀ x ∈ Icc a b, r ≤ |q x|) :
    (∫ x in a..b, q' x / q x ^ 2) = (q a)⁻¹ - (q b)⁻¹ ∧
      (∫ x in a..b, q' x / q x ^ 2) ≤ 2 / r := by
  have hne (x : ℝ) (hx : x ∈ Icc a b) : q x ≠ 0 := by
    intro hz
    have := hsep x hx
    simp only [hz, abs_zero] at this
    linarith
  have hc : ContinuousOn q (Icc a b) :=
    fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun x => q' x / q x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx))
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => -(q x)⁻¹) (q' x / q x ^ 2) x := by
    rw [uIcc_of_le hab]
    intro x hx
    simpa only [Pi.neg_apply, Pi.inv_apply, neg_div, neg_neg] using!
      ((hq x hx).inv (hne x hx)).neg
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [sub_neg_eq_add, neg_add_eq_sub] at he
  refine ⟨he, ?_⟩
  rw [he]
  have bound (x : ℝ) (hx : x ∈ Icc a b) : |(q x)⁻¹| ≤ 1 / r := by
    rw [abs_inv, one_div]
    exact inv_anti₀ hr (hsep x hx)
  calc
    (q a)⁻¹ - (q b)⁻¹ ≤ |(q a)⁻¹| + |(q b)⁻¹| := by
      linarith [le_abs_self ((q a)⁻¹), neg_le_abs ((q b)⁻¹)]
    _ ≤ 1 / r + 1 / r := add_le_add (bound a ⟨le_rfl, hab⟩) (bound b ⟨hab, le_rfl⟩)
    _ = 2 / r := by ring

lemma nonstationary_monotone_bound {a b t r C₀ C₁ : ℝ}
    (hab : a ≤ b) (ht : t ≠ 0) (hr : 0 < r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    {φ q q' : ℝ → ℝ} {A A' : ℝ → ℂ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (q x) x)
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hqc : ContinuousOn q' (Icc a b)) (hAc : ContinuousOn A' (Icc a b))
    (hqpos : ∀ x ∈ Icc a b, 0 ≤ q' x)
    (hsep : ∀ x ∈ Icc a b, r ≤ |q x|)
    (hAb : ∀ x ∈ Icc a b, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc a b, ‖A' x‖ ≤ C₁) :
    ‖∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (4 * C₀ + (b - a) * C₁) / (|t| * r) := by
  have hne (x : ℝ) (hx : x ∈ Icc a b) : q x ≠ 0 := by
    intro hz
    have := hsep x hx
    simp only [hz, abs_zero] at this
    linarith
  have hc : ContinuousOn q (Icc a b) :=
    fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hAf : ContinuousOn A (Icc a b) :=
    fun x hx => (hA x hx).continuousAt.continuousWithinAt
  let B := fun x => A x / (q x : ℂ)
  let B' := fun x => A' x / (q x : ℂ) - A x * (q' x / q x ^ 2 : ℝ)
  have hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x := by
    rw [uIcc_of_le hab]
    intro x hx
    have he : B' x = (A' x * (q x : ℂ) - A x * (q' x : ℂ)) / (q x : ℂ)^2 := by
      dsimp only [B']
      push_cast
      field_simp [ofReal_ne_zero.mpr (hne x hx)]
    rw [he]
    exact (hA x hx).div (hq x hx).ofReal_comp (ofReal_ne_zero.mpr (hne x hx))
  have hBc : ContinuousOn B' (Icc a b) := by
    dsimp [B']
    exact (hAc.div (Complex.continuous_ofReal.comp_continuousOn hc) (fun x hx => ofReal_ne_zero.mpr (hne x hx))).sub
      (hAf.mul (Complex.continuous_ofReal.comp_continuousOn
        (hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx)))))
  have hBi : IntervalIntegrable B' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hBc
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ C₀ / r := by
    dsimp [B]
    rw [norm_div, norm_real, Real.norm_eq_abs]
    exact div_le_div₀ hC₀ (hAb x hx) hr (hsep x hx)
  have hbound' (x : ℝ) (hx : x ∈ Icc a b) :
      ‖B' x‖ ≤ C₁ / r + C₀ * (q' x / q x ^ 2) := by
    dsimp [B']
    calc
      ‖A' x / (q x : ℂ) - A x * (q' x / q x ^ 2 : ℝ)‖ ≤
        ‖A' x / (q x : ℂ)‖ + ‖A x * (q' x / q x ^ 2 : ℝ)‖ := norm_sub_le _ _
      _ ≤ C₁ / r + C₀ * (q' x / q x ^ 2) := by
        apply add_le_add
        · rw [norm_div, norm_real, Real.norm_eq_abs]
          exact div_le_div₀ hC₁ (hA'b x hx) hr (hsep x hx)
        · rw [norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (hqpos x hx) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (hAb x hx)
            (div_nonneg (hqpos x hx) (sq_nonneg _))
  have hiq : IntervalIntegrable (fun x => q' x / q x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx))
  have hint : (∫ x in a..b, ‖B' x‖) ≤ (b - a) * (C₁ / r) + C₀ * (2 / r) := by
    calc
      (∫ x in a..b, ‖B' x‖) ≤ (∫ x in a..b, C₁ / r + C₀ * (q' x / q x ^ 2)) :=
        intervalIntegral.integral_mono_on hab hBi.norm
          ((intervalIntegrable_const).add (hiq.const_mul C₀)) hbound'
      _ = (b - a) * (C₁ / r) + C₀ * (∫ x in a..b, q' x / q x ^ 2) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hiq.const_mul C₀),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left
        (reciprocal_variation hab hr hq hqc hsep).2 hC₀) _
  have heq : (∫ x in a..b, B x * (q x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) =
      (∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro x hx
    simp only [B, div_mul_cancel₀ (A x) (ofReal_ne_zero.mpr (hne x hx))]
  have hh := oscillatory_integral_bound hab ht
    (φ := φ) (φ' := q) (B := B) (B' := B')
    (by simpa only [uIcc_of_le hab] using hφ) hB
    (by simpa only [uIcc_of_le hab] using hc) hBi
  rw [heq] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (1 / |t|) * (C₀ / r + C₀ / r + ((b-a) * (C₁/r) + C₀ * (2/r))) := by
      gcongr
      · exact hbound b ⟨hab, le_rfl⟩
      · exact hbound a ⟨le_rfl, hab⟩
    _ = _ := by ring

lemma cubic_taylor_estimate {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {v x M : ℝ} (hv : deriv φ v = 0)
    (hM : ∀ u ∈ uIcc v x, |iteratedDeriv 3 φ u| ≤ M) :
    |φ x - φ v - (iteratedDeriv 2 φ v) / 2 * (x - v)^2| ≤
      M * |x - v|^3 / 6 := by
  by_cases h : v = x
  · subst x
    simp
  have hu := uniqueDiffOn_uIcc h
  have ht : taylorWithinEval φ 2 (uIcc v x) v x =
      φ v + (iteratedDeriv 2 φ v) / 2 * (x - v)^2 := by
    rw [taylorWithinEval_succ φ 1, taylorWithinEval_succ φ 0, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hφ.of_le (by norm_num)).contDiffAt (left_mem_uIcc),
      iteratedDerivWithin_eq_iteratedDeriv hu (hφ.of_le (by norm_num)).contDiffAt (left_mem_uIcc)]
    simp only [iteratedDeriv_one, hv, zero_add, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, Nat.cast_zero, one_mul, pow_one, smul_eq_mul, mul_zero, add_zero]
    ring
  obtain ⟨u, hu', he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) h hφ.contDiffOn
  rw [ht] at he
  have hu'' : u ∈ uIcc v x := ⟨hu'.1.le, hu'.2.le⟩
  norm_num at he
  rw [show φ x - φ v - iteratedDeriv 2 φ v / 2 * (x-v)^2 =
    φ x - (φ v + iteratedDeriv 2 φ v / 2 * (x-v)^2) by ring, he,
      abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM u hu'') (by positivity)) (by norm_num)

lemma norm_exp_imag_sub_le (s t : ℝ) :
    ‖Complex.exp (I * (s : ℂ)) - Complex.exp (I * (t : ℂ))‖ ≤ |s - t| := by
  have he : Complex.exp (I * (s : ℂ)) - Complex.exp (I * (t : ℂ)) =
      Complex.exp (I * (t : ℂ)) * (Complex.exp (I * ((s - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s-t)

lemma local_stationary_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 1 A)
    {r t C₀ C₁ M : ℝ} (hr : 0 ≤ r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0) (hsecond : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hM : ∀ x ∈ Icc (-r) r, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ‖A 0‖ ≤ C₀) (hA'b : ∀ x ∈ Icc (-r) r, ‖deriv A x‖ ≤ C₁) :
    ‖(∫ x in -r..r, A x * Complex.exp (I * (t * φ x : ℝ))) -
        A 0 * (∫ x in -r..r, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ ≤
      2 * r * (C₁ * r + C₀ * (|t| * M * r^3 / 6)) := by
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr⟩
  have ha (x : ℝ) (hx : x ∈ Icc (-r) r) : ‖A x - A 0‖ ≤ C₁ * r := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hA.differentiable (by norm_num) x) hA'b (convex_Icc (-r) r) h0 hx
    simp only [sub_zero, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hC₁)
  have hp (x : ℝ) (hx : x ∈ Icc (-r) r) : |φ x - Real.pi * x^2| ≤ M * r^3 / 6 := by
    have h := cubic_taylor_estimate hφ hcrit (fun u hu => hM u (uIcc_subset_Icc h0 hx hu))
    simp only [hzero, hsecond, sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h
    calc
      |φ x - Real.pi * x^2| ≤ M * |x|^3 / 6 := by convert h using 1
      _ ≤ _ := by gcongr; exact abs_le.mpr hx
  have hc₁ : IntervalIntegrable (fun x => A x * Complex.exp (I * (t * φ x : ℝ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    have := hA.continuous
    have := hφ.continuous
    fun_prop
  have hc₂ : IntervalIntegrable (fun x => A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hc₁ hc₂]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := C₁*r + C₀*(|t| *M*r^3/6))
    (f := fun x => A x * Complex.exp (I * (t * φ x : ℝ)) -
      A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))
  have hpoint (x : ℝ) (hx : x ∈ Icc (-r) r) :
      ‖A x * Complex.exp (I * (t * φ x : ℝ)) -
        A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ))‖ ≤
          C₁*r + C₀*(|t| *M*r^3/6) := by
    have heq : A x * Complex.exp (I * (t * φ x : ℝ)) -
        A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ)) =
        (A x - A 0) * Complex.exp (I * (t * φ x : ℝ)) +
        A 0 * (Complex.exp (I * (t * φ x : ℝ)) -
          Complex.exp (I * (Real.pi * t * x^2 : ℝ))) := by ring
    rw [heq]
    calc
      _ ≤ ‖(A x - A 0) * Complex.exp (I * (t * φ x : ℝ))‖ +
        ‖A 0 * (Complex.exp (I * (t * φ x : ℝ)) -
          Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ := norm_add_le _ _
      _ ≤ C₁*r + C₀*(|t| *M*r^3/6) := by
        apply add_le_add
        · rw [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact ha x hx
        · rw [norm_mul]
          apply mul_le_mul hAb _ (norm_nonneg _) hC₀
          calc
            _ ≤ |t * φ x - Real.pi * t * x^2| := norm_exp_imag_sub_le _ _
            _ = |t| * |φ x - Real.pi * x^2| := by rw [← abs_mul]; congr 1; ring
            _ ≤ |t| * (M*r^3/6) := mul_le_mul_of_nonneg_left (hp x hx) (abs_nonneg _)
            _ = _ := by ring
  specialize hh (fun x hx => hpoint x (by
    rw [uIoc_of_le (by linarith : -r ≤ r)] at hx
    exact ⟨hx.1.le, hx.2⟩))
  convert hh using 1
  rw [abs_of_nonneg (by linarith : 0 ≤ r - -r)]
  ring

lemma derivative_coercive {q : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hq : Differentiable ℝ q) (hq0 : q 0 = 0)
    (hc : ∀ x ∈ Icc (-R) R, c ≤ deriv q x) :
    ∀ x ∈ Icc (-R) R, c * |x| ≤ |q x| := by
  intro x hx
  have h := (convex_Icc (-R) R).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => hc x (interior_subset hx))
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  rcases le_total 0 x with hp | hn
  · have hh := h 0 h0 x hx hp
    rw [hq0, sub_zero, sub_zero] at hh
    rw [abs_of_nonneg hp]
    exact hh.trans (le_abs_self _)
  · have hh := h x hx 0 h0 hn
    rw [hq0, zero_sub, zero_sub] at hh
    rw [abs_of_nonpos hn]
    exact hh.trans (neg_le_abs _)

lemma normalized_phase_tail {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {a b R c r t C₀ C₁ : ℝ}
    (hab : a ≤ b) (ha : -R ≤ a) (hb : b ≤ R) (ht : t ≠ 0) (hr : 0 < r)
    (hc : 0 < c) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hcrit : deriv φ 0 = 0)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hsep : ∀ x ∈ Icc a b, r ≤ |x|)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (4 * C₀ + 2 * R * C₁) / (|t| * (c * r)) := by
  have hR : 0 ≤ R := by linarith
  have hsub : Icc a b ⊆ Icc (-R) R := Icc_subset_Icc ha hb
  have hq : ContDiff ℝ 2 (deriv φ) := by simpa using (hφ.of_le (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).deriv'
  have hqa : Differentiable ℝ (deriv φ) := hq.differentiable (by norm_num)
  have hd : ∀ x, deriv (deriv φ) x = iteratedDeriv 2 φ x := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hco := derivative_coercive hR hqa hcrit (by simpa only [hd] using hsecond)
  have h := nonstationary_monotone_bound hab ht (mul_pos hc hr) hC₀ hC₁
    (φ := φ) (q := deriv φ) (q' := deriv (deriv φ)) (A := A) (A' := deriv A)
    (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hqa x).hasDerivAt)
    (fun x _ => (hA.differentiable (by norm_num) x).hasDerivAt)
    (hq.continuous_deriv (by norm_num)).continuousOn
    (hA.continuous_deriv (by norm_num)).continuousOn
    (fun x hx => hc.le.trans (by simpa only [hd] using hsecond x (hsub hx)))
    (fun x hx => (mul_le_mul_of_nonneg_left (hsep x hx) hc.le).trans (hco x (hsub hx)))
    (fun x hx => hAb x (hsub hx)) (fun x hx => hA'b x (hsub hx))
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr
  linarith

lemma quadratic_phase_deriv (x : ℝ) : deriv (fun x : ℝ => Real.pi*x^2) x = 2*Real.pi*x := by
  convert ((hasDerivAt_id x).pow 2).const_mul Real.pi |>.deriv using 1 <;>
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one]; ring

lemma quadratic_phase_second (x : ℝ) : iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) x = 2*Real.pi := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (fun x : ℝ => Real.pi*x^2) = fun x => 2*Real.pi*x from funext quadratic_phase_deriv]
  exact ((hasDerivAt_id x).const_mul (2*Real.pi)).deriv.trans (mul_one _)

lemma interval_three_parts {F : ℝ → ℂ} (hF : Continuous F) (R r : ℝ) :
    (∫ x in -R..R, F x) = ((∫ x in -R..-r, F x) + (∫ x in -r..r, F x)) +
      (∫ x in r..R, F x) := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]

lemma stationary_interval_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {R c r t C₀ C₁ M : ℝ} (hr : 0 < r) (hrR : r ≤ R) (ht : t ≠ 0)
    (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0)
    (hsecond0 : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hM : ∀ x ∈ Icc (-R) R, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖(∫ x in -R..R, A x * Complex.exp (I * (t * φ x : ℝ))) -
        A 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ ≤
      2 * r * (C₁ * r + C₀ * (|t| * M * r^3 / 6)) +
        4 * ((4*C₀ + 2*R*C₁) / (|t| * (c*r))) := by
  have hR : 0 ≤ R := hr.le.trans hrR
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  have hsub : Icc (-r) r ⊆ Icc (-R) R := Icc_subset_Icc (neg_le_neg hrR) hrR
  let F : ℝ → ℂ := fun x => A x * Complex.exp (I * (t * φ x : ℝ))
  let Q : ℝ → ℂ := fun x => A 0 * Complex.exp (I * (t * (Real.pi * x^2) : ℝ))
  let K := (4*C₀ + 2*R*C₁) / (|t| * (c*r))
  have hFc : Continuous F := by have := hA.continuous; have := hφ.continuous; fun_prop
  have hQc : Continuous Q := by fun_prop
  have hFL : ‖∫ x in -R..-r, F x‖ ≤ K :=
    normalized_phase_tail hφ hA (neg_le_neg hrR) le_rfl (by linarith) ht hr hc hC₀ hC₁
      hcrit hsecond (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]) hAb hA'b
  have hFR : ‖∫ x in r..R, F x‖ ≤ K :=
    normalized_phase_tail hφ hA hrR (by linarith) le_rfl ht hr hc hC₀ hC₁
      hcrit hsecond (fun x hx => (le_abs_self x).trans' hx.1) hAb hA'b
  have hqsm : ContDiff ℝ 3 (fun x : ℝ => Real.pi*x^2) := by fun_prop
  have hq0 : deriv (fun x : ℝ => Real.pi*x^2) 0 = 0 := by rw [quadratic_phase_deriv]; ring
  have hqsec : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) x := by
    intro x _; rwa [quadratic_phase_second]
  have hB : ContDiff ℝ 2 (fun _ : ℝ => A 0) := contDiff_const
  have hBb : ∀ x ∈ Icc (-R) R, ‖(fun _ : ℝ => A 0) x‖ ≤ C₀ := fun _ _ => hAb 0 h0
  have hB'b : ∀ x ∈ Icc (-R) R, ‖deriv (fun _ : ℝ => A 0) x‖ ≤ C₁ := by
    intro x _; simpa using hC₁
  have hQL : ‖∫ x in -R..-r, Q x‖ ≤ K :=
    normalized_phase_tail hqsm hB (neg_le_neg hrR) le_rfl (by linarith) ht hr hc hC₀ hC₁
      hq0 hqsec (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]) hBb hB'b
  have hQR : ‖∫ x in r..R, Q x‖ ≤ K :=
    normalized_phase_tail hqsm hB hrR (by linarith) le_rfl ht hr hc hC₀ hC₁
      hq0 hqsec (fun x hx => (le_abs_self x).trans' hx.1) hBb hB'b
  have hlocal := local_stationary_comparison hφ (hA.of_le (by norm_num))
    hr.le hC₀ hC₁ hM₀ hzero hcrit hsecond0
    (fun x hx => hM x (hsub hx)) (hAb 0 h0) (fun x hx => hA'b x (hsub hx)) (t := t)
  have heQ (a b : ℝ) : (∫ x in a..b, Q x) =
      A 0 * (∫ x in a..b, Complex.exp (I * (Real.pi * t * x^2 : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; dsimp [Q]; congr 3; ring_nf
  rw [← heQ, interval_three_parts hFc R r, interval_three_parts hQc R r]
  rw [← heQ (-r) r] at hlocal
  have he : ((∫ x in -R..-r, F x) + (∫ x in -r..r, F x) + (∫ x in r..R, F x)) -
      ((∫ x in -R..-r, Q x) + (∫ x in -r..r, Q x) + (∫ x in r..R, Q x)) =
      ((∫ x in -r..r, F x) - (∫ x in -r..r, Q x)) +
        ((∫ x in -R..-r, F x) - (∫ x in -R..-r, Q x)) +
        ((∫ x in r..R, F x) - (∫ x in r..R, Q x)) := by ring
  rw [he]
  calc
    _ ≤ (‖(∫ x in -r..r, F x) - (∫ x in -r..r, Q x)‖ +
      ‖(∫ x in -R..-r, F x) - (∫ x in -R..-r, Q x)‖) +
      ‖(∫ x in r..R, F x) - (∫ x in r..R, Q x)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2*r*(C₁*r+C₀*(|t| *M*r^3/6)) + (K+K)) + (K+K) := by
      exact add_le_add (add_le_add hlocal ((norm_sub_le _ _).trans (add_le_add hFL hQL)))
        ((norm_sub_le _ _).trans (add_le_add hFR hQR))
    _ = _ := by dsimp [K]; ring

lemma stationary_interval_scaled_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {R c s C₀ C₁ M : ℝ} (hs : 0 < s) (hrR : 1/s^4 ≤ R)
    (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0)
    (hsecond0 : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hM : ∀ x ∈ Icc (-R) R, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖(Real.sqrt (s^10) : ℂ) * ((∫ x in -R..R, A x * Complex.exp (I * (s^10 * φ x : ℝ))) -
        A 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * s^10 * x^2 : ℝ))))‖ ≤
      2*C₁/s^3 + C₀*M/(3*s) + 4*(4*C₀+2*R*C₁)/(c*s) := by
  have he : Real.sqrt (s^10) = s^5 := by
    rw [show s^10 = (s^5)^2 by ring, Real.sqrt_sq (by positivity)]
  rw [norm_mul, norm_real, Real.norm_eq_abs, he, abs_of_pos (pow_pos hs 5)]
  have h := stationary_interval_comparison hφ hA (by positivity : 0 < 1/s^4) hrR
    (pow_ne_zero 10 hs.ne') hc hπ hC₀ hC₁ hM₀ hzero hcrit hsecond0 hsecond hM hAb hA'b
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ s^5)
  refine hh.trans_eq ?_
  rw [abs_of_pos (pow_pos hs 10)]
  field_simp
  ring

lemma stationary_interval_comparison_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      ((∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
        A a 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))))
      (fun _ => 0) atTop := by
  let s : ℝ → ℝ := fun t => t ^ ((10 : ℝ)⁻¹)
  have hst : Tendsto s atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hr : Tendsto (fun t : ℝ => 1/(s t)^4) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hst)
  have hlim : Tendsto (fun t : ℝ =>
      2*C₁/(s t)^3 + C₀*M/(3*(s t)) + 4*(4*C₀+2*R*C₁)/(c*(s t))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t => 2*C₁/(s t)^3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hst)
    have h₂ : Tendsto (fun t => C₀*M/(3*(s t))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) hst)
    have h₃ : Tendsto (fun t => 4*(4*C₀+2*R*C₁)/(c*(s t))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hc hst)
    simpa only [add_zero] using Tendsto.add (Tendsto.add h₁ h₂) h₃
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hr.eventually (gt_mem_nhds hR),
    hlim.eventually (gt_mem_nhds hε)] with t ht htR htε
  intro a
  have hs : 0 < s t := Real.rpow_pos_of_pos ht _
  have he : (s t)^10 = t := Real.rpow_inv_natCast_pow ht.le (by norm_num)
  rw [dist_comm, dist_zero_right]
  have hh := stationary_interval_scaled_comparison (hφ a) (hA a) hs htR.le hc hπ hC₀ hC₁ hM₀
    (hzero a) (hcrit a) (hsecond0 a) (hsecond a) (hM a) (hAb a) (hA'b a)
  rw [he] at hh
  exact hh.trans_lt htε

lemma quadratic_phase_third (x : ℝ) : iteratedDeriv 3 (fun x : ℝ => Real.pi*x^2) x = 0 := by
  rw [iteratedDeriv_succ,
    show iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) = fun _ => 2*Real.pi from funext quadratic_phase_second]
  exact deriv_const x (2*Real.pi)

lemma quadratic_interval_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I))) := by
  let b : ContDiffBump (0 : ℝ) := ⟨R/4, R/2, by positivity, by linarith⟩
  let B : ℝ → ℂ := fun x => (b x : ℂ)
  have hBsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  have hB0 : B 0 = 1 := by
    dsimp [B]
    rw [b.one_of_mem_closedBall (by simp [b]; positivity)]
    exact ofReal_one
  have hBb (x : ℝ) : ‖B x‖ ≤ 1 := by
    simp only [B, norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hBsm.continuous_deriv (by norm_num)).continuousOn (s := Icc (-R) R)
  have hC₁pos : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 h0)
  have hQsm : ContDiff ℝ 3 (fun x : ℝ => Real.pi*x^2) := by fun_prop
  have hQ0 : deriv (fun x : ℝ => Real.pi*x^2) 0 = 0 := by rw [quadratic_phase_deriv]; ring
  have hu := stationary_interval_comparison_uniform
    (α := Unit) (φ := fun _ x => Real.pi*x^2) (A := fun _ => B)
    (fun _ => hQsm) (fun _ => hBsm.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hR
    (c := 2*Real.pi) (by positivity) le_rfl (C₀ := 1) (by norm_num) hC₁pos
    (M := 0) (by norm_num) (fun _ => by simp) (fun _ => hQ0)
    (fun _ => quadratic_phase_second 0)
    (fun _ x _ => by rw [quadratic_phase_second])
    (fun _ x _ => by rw [quadratic_phase_third]; simp)
    (fun _ x _ => hBb x) (fun _ x hx => hC₁ x hx)
  have hdiff := hu.tendsto_at ()
  simp only [hB0, one_mul] at hdiff
  have hsupport : Function.support B ⊆ Ioc (-R) R := by
    intro x hx
    have hbx : x ∈ Function.support (b : ℝ → ℝ) := by
      simpa only [Function.mem_support, B, ofReal_ne_zero] using hx
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hbx
    dsimp [b] at hbx
    exact ⟨by linarith [hbx.1], by linarith [hbx.2]⟩
  have hint (t : ℝ) : (∫ x in -R..R, B x * Complex.exp (I * (Real.pi*t*x^2 : ℝ))) =
      (∫ x : ℝ, B x * Complex.exp (I * (Real.pi*t*x^2 : ℝ))) :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_left _ _).trans hsupport)
  have hbcomp : HasCompactSupport B := b.hasCompactSupport.comp_left ofReal_zero
  have hBlim := quadratic_stationary_compact hbcomp hBsm
  simp only [hB0, mul_one] at hBlim
  simp_rw [← hint] at hBlim
  have he (t x : ℝ) : t*(Real.pi*x^2) = Real.pi*t*x^2 := by ring
  simp only [he] at hdiff
  have hh := hBlim.sub hdiff
  simp only [sub_zero] at hh
  convert hh using 1
  ext t
  ring

lemma stationary_normalized_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun a => A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I)) atTop := by
  have hu := stationary_interval_comparison_uniform hφ hA hR hc hπ hC₀ hC₁ hM₀
    hzero hcrit hsecond0 hsecond hM hAb hA'b
  have hQ := quadratic_interval_limit hR
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hε' : 0 < ε / (2 * (C₀ + 1)) := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.mp hu (ε/2) (by positivity),
    (tendsto_def.mp hQ) _ (Metric.ball_mem_nhds _ hε')] with t ht hQt
  intro a
  change dist _ _ < _ at hQt
  rw [dist_eq_norm] at hQt
  have hh := ht a
  rw [dist_comm, dist_zero_right] at hh
  rw [dist_comm, dist_eq_norm]
  have he : (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      A a 0 * Complex.exp ((Real.pi : ℂ)/4*I) =
    (Real.sqrt t : ℂ) * ((∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      A a 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ)))) +
      A a 0 * ((Real.sqrt t : ℂ) * (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ)/4*I)) := by ring
  rw [he]
  refine (norm_add_le _ _).trans_lt ?_
  have hprod : ‖A a 0 * ((Real.sqrt t : ℂ) *
      (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ)/4*I))‖ < ε/2 := by
    rw [norm_mul]
    calc
      _ ≤ C₀ * ‖(Real.sqrt t : ℂ) *
        (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
          Complex.exp ((Real.pi : ℂ)/4*I)‖ := mul_le_mul_of_nonneg_right (hAb a 0 h0) (norm_nonneg _)
      _ < (C₀+1) * (ε/(2*(C₀+1))) := by
        exact (mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ C₀+1) (norm_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left hQt (by positivity))
      _ = ε/2 := by field_simp
  linarith

lemma uniform_rescale {α : Type*} {F : ℝ → α → ℂ} {f b : α → ℂ} {k : α → ℝ}
    (hF : TendstoUniformly F f atTop) {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    (hk : ∀ a, κ ≤ k a) (hb : ∀ a, ‖b a‖ ≤ C) :
    TendstoUniformly (fun t : ℝ => fun a => b a * F (t*k a) a)
      (fun a => b a * f a) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : 0 < ε/(C+1) := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hF (ε/(C+1)) he)
  filter_upwards [eventually_ge_atTop (max 0 (T/κ))] with t ht
  intro a
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htk : T ≤ t*k a := by
    calc
      T = (T/κ)*κ := by field_simp
      _ ≤ t*κ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans ht) hκ.le
      _ ≤ t*k a := mul_le_mul_of_nonneg_left (hk a) ht0
  have h := hT (t*k a) htk a
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  rw [dist_eq_norm] at h
  calc
    _ ≤ (C+1) * ‖f a - F (t*k a) a‖ :=
      mul_le_mul_of_nonneg_right ((hb a).trans (by linarith)) (norm_nonneg _)
    _ < (C+1) * (ε/(C+1)) := mul_lt_mul_of_pos_left h (by positivity)
    _ = ε := by field_simp

lemma stationary_positive_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun a => (Real.sqrt (k a) : ℂ)⁻¹ * (A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I))) atTop := by
  have hkpos (a : α) : 0 < k a := hκ.trans_le (hk a)
  let ψ : α → ℝ → ℝ := fun a x => (k a)⁻¹ * φ a x
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := contDiff_const.mul (hφ a)
  have hψ0 (a : α) : ψ a 0 = 0 := by simp [ψ, hzero]
  have hψcrit (a : α) : deriv (ψ a) 0 = 0 := by
    simp only [ψ, deriv_const_mul_field, hcrit, mul_zero]
  have hψsecond0 (a : α) : iteratedDeriv 2 (ψ a) 0 = 2 * Real.pi := by
    simp only [ψ, iteratedDeriv_const_mul_field, hsecond0]
    field_simp [(hkpos a).ne']
  have hψsecond (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : c ≤ iteratedDeriv 2 (ψ a) x := by
    dsimp only [ψ]
    rw [iteratedDeriv_const_mul_field, inv_mul_eq_div]
    exact (le_div_iff₀ (hkpos a)).mpr (hsecond a x hx)
  have hψM (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : |iteratedDeriv 3 (ψ a) x| ≤ M := by
    dsimp only [ψ]
    rw [iteratedDeriv_const_mul_field, inv_mul_eq_div, abs_div, abs_of_pos (hkpos a)]
    exact (div_le_iff₀ (hkpos a)).mpr (hM a x hx)
  have hu := stationary_normalized_uniform hψ hA hR hc hπ hC₀ hC₁ hM₀
    hψ0 hψcrit hψsecond0 hψsecond hψM hAb hA'b
  have hb (a : α) : ‖(Real.sqrt (k a) : ℂ)⁻¹‖ ≤ (Real.sqrt κ)⁻¹ := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_anti₀ (Real.sqrt_pos.mpr hκ) (Real.sqrt_le_sqrt (hk a))
  have hv := uniform_rescale hu hκ (by positivity : 0 ≤ (Real.sqrt κ)⁻¹) hk hb
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hv ε hε, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro a
  have he (x : ℝ) : (t*k a) * ψ a x = t * φ a x := by
    dsimp [ψ]
    field_simp [(hkpos a).ne']
  have hs : (Real.sqrt (k a) : ℂ)⁻¹ * (Real.sqrt (t*k a) : ℂ) = (Real.sqrt t : ℂ) := by
    rw [Real.sqrt_mul ht0, ofReal_mul]
    field_simp [ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hkpos a)).ne']
  have hh := ht a
  simp_rw [he] at hh
  simpa only [← mul_assoc, hs] using hh

lemma stationary_positive_error_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => φ a x - φ a 0
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).sub contDiff_const
  have hψD (a : α) : deriv (ψ a) 0 = 0 := by
    dsimp only [ψ]; rw [deriv_sub_const, hcrit]
  have hψDD (a : α) (n : ℕ) (hn : 0 < n) (x : ℝ) :
      iteratedDeriv n (ψ a) x = iteratedDeriv n (φ a) x := by
    simpa only [ψ, sub_eq_add_neg, add_comm] using
      (iteratedDeriv_const_add (f := φ a) (x := x) hn (-φ a 0))
  have hu := stationary_positive_uniform hψ hA hR hc hπ hκ hk hC₀ hC₁ hM₀
    (fun a => sub_self _) hψD (by simpa only [hψDD _ 2 (by norm_num)] using hsecond0)
    (by simpa only [hψDD _ 2 (by norm_num)] using hsecond)
    (by simpa only [hψDD _ 3 (by norm_num)] using hM) hAb hA'b
  have hi (a : α) (t : ℝ) :
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) =
      Complex.exp (I * (t * φ a 0 : ℝ)) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [show Complex.exp (I * (t * φ a 0 : ℝ)) *
      (A a x * Complex.exp (I * (t * ψ a x : ℝ))) = A a x *
        (Complex.exp (I * (t * φ a 0 : ℝ)) * Complex.exp (I * (t * ψ a x : ℝ))) by ring,
      ← Complex.exp_add]
    congr 2
    dsimp [ψ]
    push_cast
    ring
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with t ht
  intro a
  rw [dist_comm, dist_zero_right, hi]
  have he : (Real.sqrt t : ℂ) * (Complex.exp (I * (t * φ a 0 : ℝ)) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ)))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp ((Real.pi : ℂ)/4*I))) =
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt t : ℂ) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ))) -
        (Real.sqrt (k a) : ℂ)⁻¹ * (A a 0 * Complex.exp ((Real.pi : ℂ)/4*I))) := by ring
  rw [he, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [dist_eq_norm, norm_sub_rev] using ht a

lemma deriv_conj_real {A : ℝ → ℂ} (hA : Differentiable ℝ A) (x : ℝ) :
    deriv (fun x => (starRingEnd ℂ) (A x)) x = (starRingEnd ℂ) (deriv A x) :=
  (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
    (hA x).hasDerivAt).deriv

lemma intervalIntegral_conj {a b : ℝ} (F : ℝ → ℂ) :
    (∫ x in a..b, (starRingEnd ℂ) (F x)) = (starRingEnd ℂ) (∫ x in a..b, F x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

lemma stationary_negative_error_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = -(2 * Real.pi * k a))
    (hsecond : ∀ a x, x ∈ Icc (-R) R → iteratedDeriv 2 (φ a) x ≤ -(c*k a))
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp (-((Real.pi : ℂ) / 4 * I)))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => -(φ a x)
  let B : α → ℝ → ℂ := fun a x => (starRingEnd ℂ) (A a x)
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).neg
  have hB (a : α) : ContDiff ℝ 2 (B a) := Complex.conjCLE.contDiff.comp (hA a)
  have hu := stationary_positive_error_uniform hψ hB hR hc hπ hκ hk hC₀ hC₁ hM₀
    (by intro a; simp [ψ, hcrit])
    (by intro a; simp [ψ, hsecond0])
    (by intro a x hx; simpa [ψ] using neg_le_neg (hsecond a x hx))
    (by simpa [ψ] using hM)
    (by simpa [B] using hAb)
    (by intro a x hx; simpa [B, deriv_conj_real ((hA a).differentiable (by norm_num))]
          using hA'b a x hx)
  have he (a : α) (t : ℝ) :
      (starRingEnd ℂ) ((Real.sqrt t : ℂ) * (∫ x in -R..R, B a x * Complex.exp (I * (t * ψ a x : ℝ))) -
        Complex.exp (I * (t * ψ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
          (B a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I)))) =
      (Real.sqrt t : ℂ) * (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
        Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
          (A a 0 * Complex.exp (-((Real.pi : ℂ) / 4 * I)))) := by
    simp only [map_sub, map_mul, map_inv₀, conj_ofReal, ← intervalIntegral_conj,
      ← Complex.exp_conj, ψ, B, conj_conj, conj_I, map_div₀, map_ofNat]
    simp only [neg_mul, mul_neg, ofReal_neg, neg_neg]
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with t ht
  intro a
  rw [← he, dist_zero_left, Complex.norm_conj]
  simpa only [dist_zero_left] using ht a

lemma nonstationary_scaled_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u : α → ℝ} {r C₀ C₁ D : ℝ} (hr : 0 < r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hlu : ∀ a, l a ≤ u a) (hD : ∀ a, u a - l a ≤ D)
    (hsecond : ∀ a x, x ∈ Icc (l a) (u a) → 0 ≤ iteratedDeriv 2 (φ a) x)
    (hsep : ∀ a x, x ∈ Icc (l a) (u a) → r ≤ |deriv (φ a) x|)
    (hAb : ∀ a x, x ∈ Icc (l a) (u a) → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l a) (u a) → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l a..u a, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun _ => 0) atTop := by
  have hbound (a : α) {t : ℝ} (ht : 0 < t) :
      ‖(Real.sqrt t : ℂ) * (∫ x in l a..u a, A a x * Complex.exp (I * (t * φ a x : ℝ)))‖ ≤
        ((4*C₀+D*C₁)/r) / Real.sqrt t := by
    have hq : ContDiff ℝ 2 (deriv (φ a)) := by
      simpa using ((hφ a).of_le (by norm_num : (2 : WithTop ℕ∞)+1 ≤ 3)).deriv'
    have hh := nonstationary_monotone_bound (hlu a) ht.ne' hr hC₀ hC₁
      (φ := φ a) (q := deriv (φ a)) (q' := deriv (deriv (φ a))) (A := A a) (A' := deriv (A a))
      (fun x _ => ((hφ a).differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => ((hA a).differentiable (by norm_num) x).hasDerivAt)
      (hq.continuous_deriv (by norm_num)).continuousOn
      ((hA a).continuous_deriv (by norm_num)).continuousOn
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hsecond a)
      (hsep a) (hAb a) (hA'b a)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    calc
      _ ≤ Real.sqrt t * ((4*C₀+(u a-l a)*C₁)/(|t| * r)) :=
        mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg t)
      _ ≤ Real.sqrt t * ((4*C₀+D*C₁)/(t*r)) := by
        rw [abs_of_pos ht]
        gcongr
        exact hD a
      _ = _ := by
        have hs := Real.sq_sqrt ht.le
        have hs0 := (Real.sqrt_pos.mpr ht).ne'
        field_simp
        rw [hs]
        ring
  have hlim := Real.tendsto_sqrt_atTop.const_div_atTop ((4*C₀+D*C₁)/r)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro a
  rw [dist_zero_left]
  exact (hbound a ht0).trans_lt ht

lemma derivative_coercive_center {q : ℝ → ℝ} {l u v c : ℝ}
    (hq : Differentiable ℝ q) (hv : v ∈ Icc l u) (hqv : q v = 0)
    (hc : ∀ x ∈ Icc l u, c ≤ deriv q x) :
    ∀ x ∈ Icc l u, c * |x-v| ≤ |q x| := by
  intro x hx
  have h := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => hc x (interior_subset hx))
  rcases le_total v x with hp | hn
  · have hh := h v hv x hx hp
    rw [hqv, sub_zero] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hp)]
    exact hh.trans (le_abs_self _)
  · have hh := h x hx v hv hn
    rw [hqv, zero_sub, ← neg_sub x v, mul_neg] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr hn)]
    simpa only [mul_neg] using hh.trans (neg_le_abs _)

lemma stationary_positive_moving_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) (v a) = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc l u → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => φ a (x+v a)
  let B : α → ℝ → ℂ := fun a x => A a (x+v a)
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).comp (contDiff_id.add contDiff_const)
  have hB (a : α) : ContDiff ℝ 2 (B a) := (hA a).comp (contDiff_id.add contDiff_const)
  have hi (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : x+v a ∈ Icc l u := by
    constructor <;> have := hv a <;> rcases hx with ⟨hx₁,hx₂⟩ <;> linarith
  have hcenter := stationary_positive_error_uniform hψ hB hR hc hπ hκ hk hC₀ hC₁ hM₀
    (by intro a; simpa only [ψ, deriv_comp_add_const, zero_add] using hcrit a)
    (by intro a; simpa only [ψ, iteratedDeriv_comp_add_const, zero_add] using hsecond0 a)
    (by intro a x hx; simpa only [ψ, iteratedDeriv_comp_add_const] using hsecond a (x+v a) (hi a x hx))
    (by intro a x hx; simpa only [ψ, iteratedDeriv_comp_add_const] using hM a (x+v a) (hi a x hx))
    (by intro a x hx; exact hAb a (x+v a) (hi a x hx))
    (by intro a x hx; simpa only [B, deriv_comp_add_const] using hA'b a (x+v a) (hi a x hx))
  have htt (a : α) (t : ℝ) : (∫ x in -R..R, B a x * Complex.exp (I * (t * ψ a x : ℝ))) =
      ∫ x in v a-R..v a+R, A a x * Complex.exp (I * (t * φ a x : ℝ)) := by
    simpa only [B, ψ, neg_add_eq_sub, add_comm R (v a)] using
      intervalIntegral.integral_comp_add_right (a := -R) (b := R)
        (fun x => A a x * Complex.exp (I * (t * φ a x : ℝ))) (v a)
  simp_rw [htt] at hcenter
  have hpos (a : α) (x : ℝ) (hx : x ∈ Icc l u) : 0 ≤ iteratedDeriv 2 (φ a) x :=
    (mul_pos hc (hκ.trans_le (hk a))).le.trans (hsecond a x hx)
  have hco (a : α) (x : ℝ) (hx : x ∈ Icc l u) : c*κ*|x-v a| ≤ |deriv (φ a) x| := by
    apply derivative_coercive_center
      (((hφ a).deriv' : ContDiff ℝ 2 (deriv (φ a))).differentiable (by norm_num))
      (c := c*κ) (v := v a) (by constructor <;> have := hv a <;> linarith) (hcrit a) _ x hx
    intro y hy
    have := (mul_le_mul_of_nonneg_left (hk a) hc.le).trans (hsecond a y hy)
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using this
  have hleftsub (a : α) : Icc l (v a-R) ⊆ Icc l u :=
    Icc_subset_Icc le_rfl (by have := hv a; linarith)
  have hrightsub (a : α) : Icc (v a+R) u ⊆ Icc l u :=
    Icc_subset_Icc (by have := hv a; linarith) le_rfl
  have hleft := nonstationary_scaled_uniform hφ hA (mul_pos (mul_pos hc hκ) hR) hC₀ hC₁
    (l := fun _ => l) (u := fun a => v a-R) (D := u-l)
    (by intro a; have := hv a; linarith) (by intro a; have := hv a; linarith)
    (fun a x hx => hpos a x (hleftsub a hx))
    (by intro a x hx
        apply le_trans _ (hco a x (hleftsub a hx))
        apply mul_le_mul_of_nonneg_left _ (mul_pos hc hκ).le
        rw [abs_of_nonpos (by rcases hx with ⟨h₁,h₂⟩; linarith)]
        rcases hx with ⟨h₁,h₂⟩; linarith)
    (fun a x hx => hAb a x (hleftsub a hx)) (fun a x hx => hA'b a x (hleftsub a hx))
  have hright := nonstationary_scaled_uniform hφ hA (mul_pos (mul_pos hc hκ) hR) hC₀ hC₁
    (l := fun a => v a+R) (u := fun _ => u) (D := u-l)
    (by intro a; have := hv a; linarith) (by intro a; have := hv a; linarith)
    (fun a x hx => hpos a x (hrightsub a hx))
    (by intro a x hx
        apply le_trans _ (hco a x (hrightsub a hx))
        apply mul_le_mul_of_nonneg_left _ (mul_pos hc hκ).le
        rw [abs_of_nonneg (by rcases hx with ⟨h₁,h₂⟩; linarith)]
        rcases hx with ⟨h₁,h₂⟩; linarith)
    (fun a x hx => hAb a x (hrightsub a hx)) (fun a x hx => hA'b a x (hrightsub a hx))
  convert (hleft.add hcenter).add hright using 1
  · ext t a
    dsimp only [Pi.add_apply, B, ψ, zero_add]
    have hF : Continuous (fun x => A a x * Complex.exp (I * (t * φ a x : ℝ))) := by fun_prop
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (a := l) (b := v a-R))
      (hF.intervalIntegrable (μ := volume) (a := v a-R) (b := v a+R))
    have hs' := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (a := l) (b := v a+R))
      (hF.intervalIntegrable (μ := volume) (a := v a+R) (b := u))
    rw [← hs', ← hs]
    ring_nf
  · ext a; simp

lemma stationary_negative_moving_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) (v a) = -(2 * Real.pi * k a))
    (hsecond : ∀ a x, x ∈ Icc l u → iteratedDeriv 2 (φ a) x ≤ -(c*k a))
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a (v a) * Complex.exp (-((Real.pi : ℂ) / 4 * I)))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => -(φ a x)
  let B : α → ℝ → ℂ := fun a x => (starRingEnd ℂ) (A a x)
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).neg
  have hB (a : α) : ContDiff ℝ 2 (B a) := Complex.conjCLE.contDiff.comp (hA a)
  have hu := stationary_positive_moving_uniform hψ hB hR hc hπ hκ hk hC₀ hC₁ hM₀ hv
    (by intro a; simp [ψ, hcrit])
    (by intro a; simp [ψ, hsecond0])
    (by intro a x hx; simpa [ψ] using neg_le_neg (hsecond a x hx))
    (by simpa [ψ] using hM)
    (by simpa [B] using hAb)
    (by intro a x hx; simpa [B, deriv_conj_real ((hA a).differentiable (by norm_num))]
          using hA'b a x hx)
  have he (a : α) (t : ℝ) :
      (starRingEnd ℂ) ((Real.sqrt t : ℂ) * (∫ x in l..u, B a x * Complex.exp (I * (t * ψ a x : ℝ))) -
        Complex.exp (I * (t * ψ a (v a) : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
          (B a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I)))) =
      (Real.sqrt t : ℂ) * (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
        Complex.exp (I * (t * φ a (v a) : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
          (A a (v a) * Complex.exp (-((Real.pi : ℂ) / 4 * I)))) := by
    simp only [map_sub, map_mul, map_inv₀, conj_ofReal, ← intervalIntegral_conj,
      ← Complex.exp_conj, ψ, B, conj_conj, conj_I, map_div₀, map_ofNat]
    simp only [neg_mul, mul_neg, ofReal_neg, neg_neg]
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with t ht
  intro a
  rw [← he, dist_zero_left, Complex.norm_conj]
  simpa only [dist_zero_left] using ht a

/-- Uniform stationary phase with ordinary lower and upper curvature bounds. -/
lemma stationary_positive_moving_of_bounds {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R d D C₀ C₁ M : ℝ} (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond : ∀ a x, x ∈ Icc l u → d ≤ iteratedDeriv 2 (φ a) x)
    (hupper : ∀ a x, x ∈ Icc l u → iteratedDeriv 2 (φ a) x ≤ D)
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) *
        ((Real.sqrt (iteratedDeriv 2 (φ a) (v a) / (2*Real.pi)) : ℂ)⁻¹ *
          (A a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  have hπ : 0 < 2*Real.pi := by positivity
  have hD : 0 < D := hd.trans_le hdD
  have hv' (a : α) : v a ∈ Icc l u := by
    constructor <;> have := hv a <;> linarith
  let k : α → ℝ := fun a => iteratedDeriv 2 (φ a) (v a)/(2*Real.pi)
  have hk (a : α) : d/(2*Real.pi) ≤ k a :=
    div_le_div_of_nonneg_right (hsecond a (v a) (hv' a)) hπ.le
  have hk' (a : α) : k a ≤ D/(2*Real.pi) :=
    div_le_div_of_nonneg_right (hupper a (v a) (hv' a)) hπ.le
  refine stationary_positive_moving_uniform hφ hA hR (c := d*(2*Real.pi)/D)
    (div_pos (mul_pos hd hπ) hD) ?_ (div_pos hd hπ) hk hC₀ hC₁
    (M := M/(d/(2*Real.pi))) (div_nonneg hM₀ (div_pos hd hπ).le) hv hcrit ?_ ?_ ?_ hAb hA'b
  · exact (div_le_iff₀ hD).mpr (by nlinarith)
  · intro a
    field_simp
  · intro a x hx
    calc
      d*(2*Real.pi)/D*k a ≤ d*(2*Real.pi)/D*(D/(2*Real.pi)) :=
        mul_le_mul_of_nonneg_left (hk' a) (by positivity)
      _ = d := by field_simp
      _ ≤ _ := hsecond a x hx
  · intro a x hx
    apply (hM a x hx).trans
    calc
      M = (M/(d/(2*Real.pi)))*(d/(2*Real.pi)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk a) (by positivity)

lemma deriv_sub_linear_phase {Φ : ℝ → ℝ} (hΦ : Differentiable ℝ Φ) (s x : ℝ) :
    deriv (fun x => Φ x-s*x) x = deriv Φ x-s := by
  rw [deriv_fun_sub (f := Φ) (g := fun x => s*x) (hΦ x) (by fun_prop)]
  simp

lemma iteratedDeriv_sub_linear_phase {Φ : ℝ → ℝ} {n : ℕ}
    (hΦ : ContDiff ℝ n Φ) (hn : 2 ≤ n) (s x : ℝ) :
    iteratedDeriv n (fun x => Φ x-s*x) x = iteratedDeriv n Φ x := by
  rw [iteratedDeriv_fun_sub (f := Φ) (g := fun x => s*x) hΦ.contDiffAt (by fun_prop)]
  have hl : iteratedDeriv n (fun x : ℝ => s*x) x = 0 := by
    calc
      _ = s * iteratedDeriv n (id : ℝ → ℝ) x := iteratedDeriv_const_mul_field s id
      _ = 0 := by simp [iteratedDeriv_id, show n ≠ 0 by omega, show n ≠ 1 by omega]
  rw [hl, sub_zero]

/-- Actual stationary leading term: zero outside the derivative branch. -/
def stationaryLeading (Φ : ℝ → ℝ) (A : ℝ → ℂ) (l u s t : ℝ) : ℂ :=
  if s ∈ Icc (deriv Φ l) (deriv Φ u) then
    let v := Function.invFunOn (deriv Φ) (Icc l u) s
    Complex.exp (I * (t*(Φ v-s*v) : ℝ)) *
      ((Real.sqrt (iteratedDeriv 2 Φ v/(2*Real.pi)) : ℂ)⁻¹ *
        (A v * Complex.exp ((Real.pi : ℂ)/4*I)))
  else 0

lemma stationary_branch_center {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {a b : ℝ} (hab : a ≤ b) {s : ℝ} (hs : s ∈ Icc (deriv Φ a) (deriv Φ b)) :
    Function.invFunOn (deriv Φ) (Icc a b) s ∈ Icc a b ∧
      deriv Φ (Function.invFunOn (deriv Φ) (Icc a b) s) = s := by
  have hh := intermediate_value_Icc hab (hΦ.continuous_deriv (by norm_num)).continuousOn hs
  exact Function.invFunOn_pos hh

lemma intervalIntegral_phase_of_support {A : ℝ → ℂ} {a b : ℝ}
    (hA : Function.support A ⊆ Ioc a b) (Φ : ℝ → ℝ) (t : ℝ) :
    (∫ x in a..b, A x * Complex.exp (I * (t*Φ x : ℝ))) =
      ∫ x, A x * Complex.exp (I * (t*Φ x : ℝ)) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  apply hA
  exact (mul_ne_zero_iff.mp hx).1

lemma phase_nonstationary_off_branch {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d C₀ C₁ : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α ×
      {s : ℝ // s ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R))} =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2.val*x) : ℝ))))
        (fun _ => 0) atTop := by
  let β := α × {s : ℝ // s ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R))}
  let φ : β → ℝ → ℝ := fun p x => Φ x-p.2.val*x
  let B : β → ℝ → ℂ := fun p => A p.1
  have hφ (p : β) : ContDiff ℝ 3 (φ p) := hΦ.sub (contDiff_const.mul contDiff_id)
  have hB (p : β) : ContDiff ℝ 2 (B p) := hA p.1
  have hi : Icc a b ⊆ Icc (a-2*R) (b+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hq : Differentiable ℝ (deriv Φ) :=
    (hΦ.deriv' : ContDiff ℝ 2 (deriv Φ)).differentiable (by norm_num)
  have hmv := (convex_Icc (a-2*R) (b+2*R)).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => show d ≤ deriv (deriv Φ) x from by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        hsecond x (interior_subset hx))
  have hlo : a-R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hhi : b+R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hsep (p : β) (x : ℝ) (hx : x ∈ Icc a b) : d*R ≤ |deriv (φ p) x| := by
    rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num))]
    have hp := p.2.property
    simp only [mem_Icc, not_and_or, not_le] at hp
    rcases hp with hp | hp
    · have hm := hmv (a-R) hlo x (hi hx) (by rcases hx with ⟨h₁,h₂⟩; linarith)
      have hd' : d*R ≤ deriv Φ x-p.2.val := by
        have hxx : R ≤ x-(a-R) := by rcases hx with ⟨h₁,h₂⟩; linarith
        have := mul_le_mul_of_nonneg_left hxx hd.le
        linarith
      exact hd'.trans (le_abs_self _)
    · have hm := hmv x (hi hx) (b+R) hhi (by rcases hx with ⟨h₁,h₂⟩; linarith)
      have hd' : d*R ≤ -(deriv Φ x-p.2.val) := by
        have hxx : R ≤ b+R-x := by rcases hx with ⟨h₁,h₂⟩; linarith
        have := mul_le_mul_of_nonneg_left hxx hd.le
        linarith
      exact hd'.trans (neg_le_abs _)
  have hu := nonstationary_scaled_uniform hφ hB (mul_pos hd hR) hC₀ hC₁
    (l := fun _ => a) (u := fun _ => b) (D := b-a)
    (fun _ => hab) (fun _ => le_rfl)
    (by intro p x hx
        rw [iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num)]
        exact hd.le.trans (hsecond x (hi hx))) hsep
    (fun p x hx => hAb p.1 x (hi hx)) (fun p x hx => hA'b p.1 x (hi hx))
  convert hu using 1
  ext t p
  rw [intervalIntegral_phase_of_support (hsupp p.1)]

lemma phase_stationary_on_branch {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α ×
      {s : ℝ // s ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))} =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2.val*x) : ℝ))) -
        stationaryLeading Φ (A p.1) (a-R) (b+R) p.2.val t)
        (fun _ => 0) atTop := by
  let β := α × {s : ℝ // s ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))}
  let φ : β → ℝ → ℝ := fun p x => Φ x-p.2.val*x
  let B : β → ℝ → ℂ := fun p => A p.1
  let v : β → ℝ := fun p => Function.invFunOn (deriv Φ) (Icc (a-R) (b+R)) p.2.val
  have hv (p : β) : v p ∈ Icc (a-R) (b+R) ∧ deriv Φ (v p) = p.2.val :=
    stationary_branch_center (hΦ.of_le (by norm_num)) (by linarith) p.2.property
  have hφ (p : β) : ContDiff ℝ 3 (φ p) := hΦ.sub (contDiff_const.mul contDiff_id)
  have hB (p : β) : ContDiff ℝ 2 (B p) := hA p.1
  have h2 (p : β) (x : ℝ) : iteratedDeriv 2 (φ p) x = iteratedDeriv 2 Φ x :=
    iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num) p.2.val x
  have h3 (p : β) (x : ℝ) : iteratedDeriv 3 (φ p) x = iteratedDeriv 3 Φ x :=
    iteratedDeriv_sub_linear_phase hΦ (by norm_num) p.2.val x
  have hu := stationary_positive_moving_of_bounds hφ hB hR hd hdD hC₀ hC₁ hM₀
    (l := a-2*R) (u := b+2*R) (v := v)
    (by intro p; constructor <;> have := (hv p).1 <;> rcases this with ⟨h₁,h₂⟩ <;> linarith)
    (by intro p; rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num)), (hv p).2, sub_self])
    (by intro p x hx; rw [h2]; exact hsecond x hx)
    (by intro p x hx; rw [h2]; exact hupper x hx)
    (by intro p x hx; rw [h3]; exact hM x hx)
    (fun p x hx => hAb p.1 x hx) (fun p x hx => hA'b p.1 x hx)
  have hs (p : β) : Function.support (B p) ⊆ Ioc (a-2*R) (b+2*R) := by
    intro x hx
    have hh := hsupp p.1 hx
    constructor <;> rcases hh with ⟨h₁,h₂⟩ <;> linarith
  simp_rw [intervalIntegral_phase_of_support (hs _), h2] at hu
  convert hu using 1
  ext t p
  simp only [stationaryLeading, ite_eq_left p.2.property]
  rfl

/-- Compactly supported, parameter-uniform stationary phase, including the
noncritical region and zero amplitudes. No weak-convergence replacement is used. -/
lemma compact_support_stationary_uniform {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α × ℝ =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2*x) : ℝ))) -
        stationaryLeading Φ (A p.1) (a-R) (b+R) p.2 t)
        (fun _ => 0) atTop := by
  have hin := phase_stationary_on_branch hΦ hA hab hR hd hdD hC₀ hC₁ hM₀
    hsecond hupper hM hAb hA'b hsupp
  have hout := phase_nonstationary_off_branch hΦ hA hab hR hd hC₀ hC₁ hsecond hAb hA'b hsupp
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hin ε hε,
    Metric.tendstoUniformly_iff.mp hout ε hε] with t ht₁ ht₂
  intro p
  by_cases hp : p.2 ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))
  · exact ht₁ (p.1, ⟨p.2,hp⟩)
  · simpa only [stationaryLeading, ite_eq_right hp, sub_zero] using ht₂ (p.1, ⟨p.2,hp⟩)

/-- Negative curvature follows by conjugation, with the same unaltered phase. -/
lemma compact_support_stationary_negative_uniform {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ -d)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), -D ≤ iteratedDeriv 2 Φ x)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α × ℝ =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2*x) : ℝ))) -
        (starRingEnd ℂ) (stationaryLeading (fun x => -Φ x)
          (fun x => (starRingEnd ℂ) (A p.1 x)) (a-R) (b+R) (-p.2) t))
        (fun _ => 0) atTop := by
  let B : α → ℝ → ℂ := fun z x => (starRingEnd ℂ) (A z x)
  have hB (z : α) : ContDiff ℝ 2 (B z) := Complex.conjCLE.contDiff.comp (hA z)
  have hu := compact_support_stationary_uniform hΦ.neg hB hab hR hd hdD hC₀ hC₁ hM₀
    (by intro x hx; simpa using neg_le_neg (hsecond x hx))
    (by intro x hx; simpa using neg_le_neg (hupper x hx))
    (by simpa using hM) (by simpa [B] using hAb)
    (by intro z x hx; simpa [B, deriv_conj_real ((hA z).differentiable (by norm_num))]
          using hA'b z x hx)
    (by intro z; simpa [B, Function.support] using hsupp z)
  have he (t s : ℝ) (z : α) :
      (starRingEnd ℂ) ((Real.sqrt t : ℂ) *
        (∫ x, B z x * Complex.exp (I * (t*(-Φ x-(-s)*x) : ℝ)))) =
      (Real.sqrt t : ℂ) * (∫ x, A z x * Complex.exp (I * (t*(Φ x-s*x) : ℝ))) := by
    simp only [map_mul, conj_ofReal, ← integral_conj, B, conj_conj, ← exp_conj, conj_I]
    congr 2
    funext x
    congr 1
    congr 1
    push_cast
    ring
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with t ht
  intro p
  have hh := ht (p.1,-p.2)
  rw [dist_zero_left] at hh ⊢
  rw [← he, ← map_sub, Complex.norm_conj]
  exact hh

lemma norm_stationaryLeading {Φ : ℝ → ℝ} {A : ℝ → ℂ} {l u s t : ℝ}
    (hs : s ∈ Icc (deriv Φ l) (deriv Φ u)) :
    ‖stationaryLeading Φ A l u s t‖ =
      (Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s) /
        (2*Real.pi)))⁻¹ * ‖A (Function.invFunOn (deriv Φ) (Icc l u) s)‖ := by
  simp only [stationaryLeading, ite_eq_left hs, norm_mul, norm_inv]
  simp [Complex.norm_exp, mul_re, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma stationaryLeading_norm_time (Φ : ℝ → ℝ) (A : ℝ → ℂ) (l u s t t' : ℝ) :
    ‖stationaryLeading Φ A l u s t‖ = ‖stationaryLeading Φ A l u s t'‖ := by
  by_cases hs : s ∈ Icc (deriv Φ l) (deriv Φ u)
  · rw [norm_stationaryLeading hs, norm_stationaryLeading hs]
  · simp only [stationaryLeading, ite_eq_right hs]

lemma stationaryLeading_bound {Φ : ℝ → ℝ} {A : ℝ → ℂ} {l u s t d C : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hlu : l ≤ u) (hd : 0 < d) (hC : 0 ≤ C)
    (hsecond : ∀ x ∈ Icc l u, d ≤ iteratedDeriv 2 Φ x)
    (hA : ∀ x ∈ Icc l u, ‖A x‖ ≤ C) :
    ‖stationaryLeading Φ A l u s t‖ ≤ C / Real.sqrt (d/(2*Real.pi)) := by
  by_cases hs : s ∈ Icc (deriv Φ l) (deriv Φ u)
  · rw [norm_stationaryLeading hs]
    have hv := (stationary_branch_center hΦ hlu hs).1
    have hd' : 0 < d/(2*Real.pi) := by positivity
    have hroot : Real.sqrt (d/(2*Real.pi)) ≤
        Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s)/(2*Real.pi)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hsecond _ hv) (by positivity))
    calc
      _ ≤ (Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s)/(2*Real.pi)))⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hA _ hv) (by positivity)
      _ ≤ (Real.sqrt (d/(2*Real.pi)))⁻¹ * C := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hd') hroot) hC
      _ = _ := by ring
  · simp only [stationaryLeading, ite_eq_right hs, norm_zero]
    positivity

lemma compact_phase_tail_bound {Φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ContDiff ℝ 2 A)
    {a b t s M C₀ C₁ : ℝ} (hab : a ≤ b) (ht : 0 < t) (hs : s ≠ 0)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsM : 2*M ≤ |s|)
    (hfirst : ∀ x ∈ Icc a b, |deriv Φ x| ≤ M)
    (hsecond : ∀ x ∈ Icc a b, 0 ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ x ∈ Icc a b, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc a b, ‖deriv A x‖ ≤ C₁)
    (hsupp : Function.support A ⊆ Ioc a b) :
    ‖∫ x, A x * Complex.exp (I * (t*(Φ x-s*x) : ℝ))‖ ≤
      2*(4*C₀+(b-a)*C₁)/(t*|s|) := by
  let φ : ℝ → ℝ := fun x => Φ x-s*x
  have hφ : ContDiff ℝ 3 φ := hΦ.sub (contDiff_const.mul contDiff_id)
  have hq : ContDiff ℝ 2 (deriv φ) := hφ.deriv'
  have hsep (x : ℝ) (hx : x ∈ Icc a b) : |s|/2 ≤ |deriv φ x| := by
    rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num))]
    have htri : |s| ≤ |deriv Φ x-s|+|deriv Φ x| := by
      calc
        _ = |deriv Φ x-(deriv Φ x-s)| := by congr 1; ring
        _ ≤ |deriv Φ x|+|deriv Φ x-s| := by simpa only [Real.norm_eq_abs] using norm_sub_le (deriv Φ x) (deriv Φ x-s)
        _ = _ := by ring
    have hh := hfirst x hx
    linarith
  have hh := nonstationary_monotone_bound hab ht.ne' (half_pos (abs_pos.mpr hs)) hC₀ hC₁
    (φ := φ) (q := deriv φ) (q' := deriv (deriv φ)) (A := A) (A' := deriv A)
    (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hA.differentiable (by norm_num) x).hasDerivAt)
    (hq.continuous_deriv (by norm_num)).continuousOn
    (hA.continuous_deriv (by norm_num)).continuousOn
    (by intro x hx
        have hh := hsecond x hx
        have he := iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num : 2 ≤ 2) s x
        simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hh.trans he.ge)
    hsep hAb hA'b
  rw [intervalIntegral_phase_of_support hsupp] at hh
  convert hh using 1
  rw [abs_of_pos ht]
  field_simp

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
namespace ThreeTorus

lemma norm_sq_difference_bound (z w : ℂ) {ε L : ℝ} (hε : 0 ≤ ε) (_hL : 0 ≤ L)
    (he : ‖z-w‖ ≤ ε) (hw : ‖w‖ ≤ L) :
    |‖z‖^2-‖w‖^2| ≤ ε*(ε+2*L) := by
  have hz : ‖z‖ ≤ ε+L := by
    calc
      ‖z‖ ≤ ‖z-w‖+‖w‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert w z
      _ ≤ _ := add_le_add he hw
  calc
    _ = |‖z‖-‖w‖| *(‖z‖+‖w‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖z‖+‖w‖)]
      ring
    _ ≤ ε*(ε+2*L) := mul_le_mul ((abs_norm_sub_norm_le z w).trans he)
      (by linarith) (by positivity) hε

lemma stationary_pointwise_mass_bound (z w : ℂ) {N ε L : ℝ} (hN : 0 < N)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (he : ‖(Real.sqrt N : ℂ)*z-w‖ ≤ ε) (hw : ‖w‖ ≤ L) :
    |‖z‖^2-N⁻¹*‖w‖^2| ≤ (ε*(ε+2*L))/N := by
  have h := norm_sq_difference_bound ((Real.sqrt N : ℂ)*z) w hε hL he hw
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hN.le] at h
  apply (le_div_iff₀ hN).mpr
  calc
    _ = |N*‖z‖^2-‖w‖^2| := by
      calc
        _ = |(‖z‖^2-N⁻¹*‖w‖^2)*N| := by rw [abs_mul, abs_of_pos hN]
        _ = _ := by congr 1; field_simp
    _ ≤ _ := h

lemma stationary_integrated_mass_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : Ω → ℂ} {N ε L : ℝ}
    (hN : 0 < N) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hi : Integrable (fun x => |‖C x‖^2-N⁻¹*‖Ld x‖^2|) μ)
    (he : ∀ x, ‖(Real.sqrt N : ℂ)*C x-Ld x‖ ≤ ε) (hw : ∀ x, ‖Ld x‖ ≤ L) :
    (∫ x, |‖C x‖^2-N⁻¹*‖Ld x‖^2| ∂μ) ≤ ε*(ε+2*L)/N := by
  calc
    _ ≤ ∫ _ : Ω, ε*(ε+2*L)/N ∂μ := integral_mono hi (integrable_const _)
      (fun x => stationary_pointwise_mass_bound (C x) (Ld x) hN hε hL (he x) (hw x))
    _ = _ := by simp

lemma integer_band_card_bound (K n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc (-(K*n : ℤ)) (K*n)).card : ℝ) ≤ (2*(K:ℝ)+1)*(n:ℝ) := by
  rw [Int.card_Icc]
  have he : ((K*n : ℤ)+1-(-(K*n : ℤ))).toNat = 2*K*n+1 := by
    have he' : (K*n : ℤ)+1-(-(K*n : ℤ)) = ((2*K*n+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he']
    exact Int.toNat_natCast _
  rw [he]
  push_cast
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma stationary_band_mass_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℤ → Ω → ℂ} {ε L : ℝ}
    (K n : ℕ) (hn : 1 ≤ n) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hi : ∀ j, Integrable (fun x => |‖C j x‖^2-(n:ℝ)⁻¹*‖Ld j x‖^2|) μ)
    (he : ∀ j x, ‖(Real.sqrt n : ℂ)*C j x-Ld j x‖ ≤ ε)
    (hw : ∀ j x, ‖Ld j x‖ ≤ L) :
    (∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), ∫ x, |‖C j x‖^2-(n:ℝ)⁻¹*‖Ld j x‖^2| ∂μ)
      ≤ (2*(K:ℝ)+1)*(ε*(ε+2*L)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), ε*(ε+2*L)/(n:ℝ) :=
      Finset.sum_le_sum (fun j _ => stationary_integrated_mass_bound hn' hε hL (hi j) (he j) (hw j))
    _ = ((Finset.Icc (-(K*n : ℤ)) (K*n)).card : ℝ)*(ε*(ε+2*L)/(n:ℝ)) := by simp
    _ ≤ ((2*(K:ℝ)+1)*(n:ℝ))*(ε*(ε+2*L)/(n:ℝ)) :=
      mul_le_mul_of_nonneg_right (integer_band_card_bound K n hn) (by positivity)
    _ = _ := by field_simp

lemma integer_band_exhausts (K : ℕ) (hK : 1 ≤ K) (j : ℤ) :
    ∀ᶠ n : ℕ in atTop, j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) := by
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  have hab : |j| ≤ (n : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  have hkn : (n : ℤ) ≤ (K : ℤ)*n := by
    have hKn : n ≤ K*n := by nlinarith
    exact_mod_cast hKn
  simpa only [Finset.mem_Icc] using abs_le.mp (hab.trans hkn)

lemma stationary_tail_mass_tendsto {E : ℕ → ℤ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    {B : ℤ → ℝ} (hB : Summable B)
    (hE0 : ∀ n j, 0 ≤ E n j)
    (hEB : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) → E n j ≤ B j) :
    Tendsto (fun n : ℕ => ∑' j : ℤ,
      if j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) then 0 else E n j) atTop (𝓝 0) := by
  classical
  have hB' : Summable (fun j => |B j|) := hB.abs
  have hh := tendsto_tsum_of_dominated_convergence (bound := fun j => |B j|) hB'
    (f := fun n : ℕ => fun j : ℤ => if j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) then 0 else E n j)
    (g := fun _ : ℤ => (0 : ℝ))
    (fun j => tendsto_const_nhds.congr' (by
      filter_upwards [integer_band_exhausts K hK j] with n hn
      simp only [ite_eq_left hn]))
    (by filter_upwards [hEB] with n hn
        intro j
        split_ifs with hj
        · simp only [norm_zero]; exact abs_nonneg _
        · rw [Real.norm_eq_abs, abs_of_nonneg (hE0 n j)]
          exact (hn j hj).trans (le_abs_self _))
  simpa only [tsum_zero] using hh

lemma stationary_tail_square_bound_summable (D : ℝ) :
    Summable (fun j : ℤ => D^2/(j:ℝ)^2) := by
  simpa only [mul_one_div] using
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (D^2))

lemma stationary_band_mass_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℕ → ℤ → Ω → ℂ} {L : ℝ}
    (K : ℕ) (hL : 0 ≤ L)
    (hi : ∀ n j, Integrable (fun x => |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2|) μ)
    (he : TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*C n p.1 p.2-Ld n p.1 p.2) (fun _ => 0) atTop)
    (hw : ∀ n j x, ‖Ld n j x‖ ≤ L) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n),
      ∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c : ℝ := 2*(K:ℝ)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let δ : ℝ := min 1 (ε/(2*c*(1+2*L)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε/(2*c*(1+2*L)) := min_le_right _ _
  have hbound : c*(δ*(δ+2*L)) < ε := by
    calc
      _ ≤ c*(δ*(1+2*L)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith : δ+2*L ≤ 1+2*L) hδ.le) hc.le
      _ ≤ c*((ε/(2*c*(1+2*L)))*(1+2*L)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hδ2 (by positivity)) hc.le
      _ = ε/2 := by field_simp
      _ < ε := by linarith
  filter_upwards [Metric.tendstoUniformly_iff.mp he δ hδ,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hb := stationary_band_mass_bound K n hn1 hδ.le hL (hi n)
    (fun j x => by simpa only [dist_zero_left] using (hn (j,x)).le) (hw n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hb.trans_lt hbound

lemma tsum_band_tail_decomposition {E B : ℤ → ℝ} (S : Finset ℤ)
    (hE : ∀ j, 0 ≤ E j) (hB : Summable B) (hEB : ∀ j ∉ S, E j ≤ B j) :
    (∑' j, E j) = (∑ j ∈ S, E j) + ∑' j, if j ∈ S then 0 else E j := by
  classical
  have hs : HasSum (fun j => if j ∈ S then E j else 0) (∑ j ∈ S, E j) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (s := S)
      (fun j hj => show (if j ∈ S then E j else 0) = 0 by simp [hj]) using 1
    exact Finset.sum_congr rfl (fun j hj => by simp [hj])
  have ht : Summable (fun j => if j ∈ S then 0 else E j) := by
    apply hB.abs.of_norm_bounded
    intro j
    split_ifs with hj
    · simp
    · rw [Real.norm_eq_abs, abs_of_nonneg (hE j)]
      exact (hEB j hj).trans (le_abs_self _)
  have hh := hs.add ht.hasSum
  have he (j : ℤ) : (if j ∈ S then E j else 0) + (if j ∈ S then 0 else E j) = E j := by
    split_ifs <;> simp
  exact (hh.congr_fun (fun j => (he j).symm)).tsum_eq

lemma tsum_tendsto_zero_of_band_and_tail {E : ℕ → ℤ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    {B : ℤ → ℝ} (hB : Summable B) (hE0 : ∀ n j, 0 ≤ E n j)
    (hEB : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) → E n j ≤ B j)
    (hc : Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), E n j) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, E n j) atTop (𝓝 0) := by
  have ht := stationary_tail_mass_tendsto hK hB hE0 hEB
  have hh := hc.add ht
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hEB] with n hn
  exact (tsum_band_tail_decomposition _ (hE0 n) hB hn).symm

/-- Summed L¹ coefficient-mass conclusion; unlike weak convergence this controls
all retained index subarrays and their pushforwards. -/
lemma summed_stationary_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℕ → ℤ → Ω → ℂ} {L D : ℝ}
    (K : ℕ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hi : ∀ n j, Integrable (fun x => |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2|) μ)
    (he : TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*C n p.1 p.2-Ld n p.1 p.2) (fun _ => 0) atTop)
    (hw : ∀ n j x, ‖Ld n j x‖ ≤ L)
    (ht : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) →
      (∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) ≤ D^2/(j:ℝ)^2) :
    Tendsto (fun n : ℕ => ∑' j : ℤ,
      ∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) atTop (𝓝 0) := by
  exact tsum_tendsto_zero_of_band_and_tail hK (stationary_tail_square_bound_summable D)
    (by intros; positivity) ht (stationary_band_mass_tendsto K hL hi he hw)

end ThreeTorus

namespace ThreeTorus

/-- Rounding is in the slow Fourier slope, not a translation of the fast variable. -/
def passageSlope (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) : ℝ := κ*(j:ℝ)/(n:ℝ)-α n

def passageCoefficient {Ω : Type*} (Φ : ℝ → ℝ) (A : Ω → ℝ → ℂ)
    (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) (z : Ω) : ℂ :=
  ∫ x, A z x * Complex.exp (I * ((n:ℝ)*(Φ x-passageSlope κ α n j*x) : ℝ))

def passageLeading {Ω : Type*} (Φ : ℝ → ℝ) (A : Ω → ℝ → ℂ)
    (a b R κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) (z : Ω) : ℂ :=
  stationaryLeading Φ (A z) (a-R) (b+R) (passageSlope κ α n j) n

lemma passage_uniform_error {Ω : Type*} {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) (κ : ℝ) (α : ℕ → ℝ) :
    TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*passageCoefficient Φ A κ α n p.1 p.2 -
        passageLeading Φ A a b R κ α n p.1 p.2) (fun _ => 0) atTop := by
  have hh := compact_support_stationary_uniform hΦ hA hab hR hd hdD hC₀ hC₁ hM₀
    hsecond hupper hM hAb hA'b hsupp
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ))
    (Metric.tendstoUniformly_iff.mp hh ε hε)] with n hn
  intro p
  exact hn (p.2, passageSlope κ α n p.1)

lemma passageSlope_large {κ C M : ℝ} {α : ℕ → ℝ} {K n : ℕ} {j : ℤ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 2*(C+M+1) ≤ κ*K)
    (hn : 1 ≤ n) (hα : |α n| ≤ C) (hj : j ∉ Finset.Icc (-(K*n : ℤ)) (K*n)) :
    2*M < |passageSlope κ α n j| ∧
      κ*|(j:ℝ)|/(2*(n:ℝ)) ≤ |passageSlope κ α n j| ∧ j ≠ 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hj' : (K:ℝ)*n < |(j:ℝ)| := by
    have hji : (K:ℤ)*n < |j| := by
      simpa only [Finset.mem_Icc, ← abs_le, not_le] using hj
    exact_mod_cast hji
  have hv : κ*K < κ*|(j:ℝ)|/(n:ℝ) := by
    apply (lt_div_iff₀ hn').mpr
    nlinarith
  have htri : κ*|(j:ℝ)|/(n:ℝ)-C ≤ |passageSlope κ α n j| := by
    have ht := abs_sub_abs_le_abs_sub (κ*(j:ℝ)/(n:ℝ)) (α n)
    rw [abs_div, abs_mul, abs_of_pos hκ, abs_of_pos hn'] at ht
    dsimp [passageSlope]
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [show κ*|(j:ℝ)|/(2*(n:ℝ)) = (κ*|(j:ℝ)|/(n:ℝ))/2 by ring]
    linarith
  · intro he
    subst j
    simp only [Int.cast_zero, abs_zero] at hj'
    have : 0 ≤ (K:ℝ)*n := by positivity
    linarith

lemma passage_arrays_tail {Ω : Type*} {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d C₀ C₁ M C κ : ℝ} {α : ℕ → ℝ} {K n : ℕ} {j : ℤ}
    (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hκ : 0 < κ) (hK : 2*(C+M+1) ≤ κ*K)
    (hn : 1 ≤ n) (hα : |α n| ≤ C)
    (hfirst : ∀ x ∈ Icc (a-2*R) (b+2*R), |deriv Φ x| ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b)
    (hj : j ∉ Finset.Icc (-(K*n:ℤ)) (K*n)) (z : Ω) :
    passageLeading Φ A a b R κ α n j z = 0 ∧
      ‖passageCoefficient Φ A κ α n j z‖ ≤ (4*(4*C₀+(b-a)*C₁)/κ)/|(j:ℝ)| := by
  obtain ⟨hlarge,hlower,hj0⟩ := passageSlope_large hκ hC hM hK hn hα hj
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsub : Icc a b ⊆ Icc (a-2*R) (b+2*R) := by intro x hx; constructor <;> linarith [hx.1,hx.2]
  have hleft : a-R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hright : b+R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hnot : passageSlope κ α n j ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R)) := by
    intro hh
    have hl := abs_le.mp (hfirst _ hleft)
    have hr := abs_le.mp (hfirst _ hright)
    have hh' : |passageSlope κ α n j| ≤ M := abs_le.mpr ⟨hl.1.trans hh.1,hh.2.trans hr.2⟩
    linarith
  refine ⟨by simp only [passageLeading, stationaryLeading, ite_eq_right hnot], ?_⟩
  have hs : passageSlope κ α n j ≠ 0 := abs_pos.mp (lt_of_le_of_lt (by positivity : 0 ≤ 2*M) hlarge)
  have hb := compact_phase_tail_bound hΦ (hA z) hab hn' hs hC₀ hC₁ hlarge.le
    (fun x hx => hfirst x (hsub hx)) (fun x hx => hd.le.trans (hsecond x (hsub hx)))
    (fun x hx => hAb z x (hsub hx)) (fun x hx => hA'b z x (hsub hx)) (hsupp z)
  apply hb.trans
  have hjpos : 0 < |(j:ℝ)| := abs_pos.mpr (by exact_mod_cast hj0)
  have hnum : 0 ≤ 2*(4*C₀+(b-a)*C₁) := by positivity
  calc
    _ ≤ (2*(4*C₀+(b-a)*C₁))/((n:ℝ)*(κ*|(j:ℝ)|/(2*(n:ℝ)))) :=
      div_le_div_of_nonneg_left hnum (by positivity) (mul_le_mul_of_nonneg_left hlower hn'.le)
    _ = _ := by field_simp; ring

/-- The strong summed mass estimate used in the passage lemma. -/
lemma passage_summed_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d D C₀ C₁ M M₁ C κ : ℝ} {α : ℕ → ℝ}
    (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hα : ∀ n, |α n| ≤ C)
    (hfirst : ∀ x ∈ Icc (a-2*R) (b+2*R), |deriv Φ x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b)
    (hi : ∀ n j, Integrable (fun z => |‖passageCoefficient Φ A κ α n j z‖^2 -
      (n:ℝ)⁻¹*‖passageLeading Φ A a b R κ α n j z‖^2|) μ) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ z,
      |‖passageCoefficient Φ A κ α n j z‖^2 -
        (n:ℝ)⁻¹*‖passageLeading Φ A a b R κ α n j z‖^2| ∂μ) atTop (𝓝 0) := by
  obtain ⟨K₀,hK₀⟩ := exists_nat_ge (2*(C+M₁+1)/κ)
  let K := max K₀ 1
  have hK : 2*(C+M₁+1) ≤ κ*K := by
    have hh : (K₀:ℝ) ≤ K := by exact_mod_cast (le_max_left K₀ 1)
    have hh' := (div_le_iff₀ hκ).mp (hK₀.trans hh)
    nlinarith
  have hK1 : 1 ≤ K := le_max_right _ _
  have hsub : Icc (a-R) (b+R) ⊆ Icc (a-2*R) (b+2*R) := by
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  apply summed_stationary_mass K hK1 (L := C₀ / Real.sqrt (d/(2*Real.pi)))
    (D := 4*(4*C₀+(b-a)*C₁)/κ) (by positivity) hi
    (passage_uniform_error hΦ hA hab hR hd hdD hC₀ hC₁ hM₀ hsecond hupper hM hAb hA'b hsupp κ α)
  · intro n j z
    exact stationaryLeading_bound (hΦ.of_le (by norm_num)) (by linarith) hd hC₀
      (fun x hx => hsecond x (hsub hx)) (fun x hx => hAb z x (hsub hx))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    intro j hj
    have hb := passage_arrays_tail hΦ hA hab hR hd hC₀ hC₁ hM₁ hC hκ hK hn (hα n)
      hfirst hsecond hAb hA'b hsupp hj
    calc
      _ ≤ ∫ _ : Ω, (4*(4*C₀+(b-a)*C₁)/κ)^2/(j:ℝ)^2 ∂μ :=
        integral_mono (hi n j) (integrable_const _) (by
          intro z
          dsimp only
          rw [(hb z).1, norm_zero, zero_pow (by omega), mul_zero, sub_zero,
            abs_of_nonneg (sq_nonneg _)]
          have hh := sq_le_sq₀ (norm_nonneg (passageCoefficient Φ A κ α n j z)) (by positivity : 0 ≤ (4*(4*C₀+(b-a)*C₁)/κ)/|(j:ℝ)|)
          have hh' := hh.mpr (hb z).2
          simpa only [div_pow, sq_abs] using hh')
      _ = _ := by simp

end ThreeTorus

end

end

end

end OAI
