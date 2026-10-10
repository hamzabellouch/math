import Mathlib

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace PlanarEndpoint

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev L2 := MeasureTheory.Lp ℂ 2 (volume : Measure Plane)

def fourier (f : L2) (ξ : Plane) : ℂ :=
  (MeasureTheory.Lp.fourierTransformₗᵢ Plane ℂ f) ((2 * Real.pi)⁻¹ • ξ)

def InHThird (f : L2) : Prop :=
  Integrable (fun ξ : Plane =>
    (1 + ‖ξ‖ ^ 2) ^ (1 / 3 : ℝ) * ‖fourier f ξ‖ ^ 2) volume

def hThirdNorm (f : L2) : ℝ :=
  Real.sqrt (((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : Plane,
    (1 + ‖ξ‖ ^ 2) ^ (1 / 3 : ℝ) * ‖fourier f ξ‖ ^ 2)

def abel (f : L2) (a : ℝ) (x : Plane) (t : ℝ) : ℂ :=
  (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • ∫ ξ : Plane,
    Complex.exp (Complex.I * ((inner ℝ x ξ - t * ‖ξ‖ ^ 2 : ℝ) : ℂ) -
      ((a * ‖ξ‖ ^ 2 : ℝ) : ℂ)) * fourier f ξ

def diskAverage (f : L2) (x : Plane) (r : ℝ) : ℂ :=
  (Real.pi * r ^ 2)⁻¹ • ∫ y in Metric.ball x r, f y

def lebesgueRepresentative (f : L2) (x : Plane) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (diskAverage f x)

def IsLebesguePoint (f : L2) (x : Plane) : Prop :=
  ∃ z : ℂ, Tendsto (fun r : ℝ =>
    (Real.pi * r ^ 2)⁻¹ * ∫ y in Metric.ball x r, ‖f y - z‖)
    (𝓝[>] (0 : ℝ)) (𝓝 0)

def MainConclusion (f : L2) : Prop :=
  ∃ E : Set Plane, volume Eᶜ = 0 ∧
    ∀ x ∈ E, IsLebesguePoint f x ∧
      ∃ u : ℝ → ℂ,
        ContinuousOn u (Ico 0 1) ∧
        u 0 = lebesgueRepresentative f x ∧
        Tendsto (diskAverage f x) (𝓝[>] (0 : ℝ)) (𝓝 (u 0)) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1,
          Tendsto (fun a => abel f a x t) (𝓝[>] (0 : ℝ)) (𝓝 (u t))) ∧
        Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 (lebesgueRepresentative f x)) ∧
        TendstoUniformlyOn (fun a t => abel f a x t) u
          (𝓝[>] (0 : ℝ)) (Ioo (0 : ℝ) 1)

end PlanarEndpoint

namespace PlanarEndpoint

lemma fourier_memLp (f : L2) : MemLp (fourier f) 2 volume := by
  let g := MeasureTheory.Lp.fourierTransformₗᵢ Plane ℂ f
  have hg := (Lp.memLp g).smul_measure
    (c := ENNReal.ofReal |(((2 * Real.pi)⁻¹) ^ Module.finrank ℝ Plane)⁻¹|)
    ENNReal.ofReal_ne_top
  have hc : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [← Measure.map_addHaar_smul (volume : Measure Plane) hc] at hg
  exact hg.comp_of_map (measurable_const_smul _).aemeasurable

def phase (x : Plane) (t : ℝ) (ξ : Plane) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ x ξ - t * ‖ξ‖ ^ 2 : ℝ) : ℂ))

@[simp] lemma norm_phase (x ξ : Plane) (t : ℝ) : ‖phase x t ξ‖ = 1 := by
  simp only [phase, Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma continuous_phase (x : Plane) (t : ℝ) : Continuous (phase x t) := by
  unfold phase
  fun_prop

lemma continuous_phase_parameters (ξ : Plane) :
    Continuous (fun z : Plane × ℝ => phase z.1 z.2 ξ) := by
  unfold phase
  fun_prop

lemma memLp_gaussian {a : ℝ} (ha : 0 < a) :
    MemLp (fun ξ : Plane => Complex.exp (-((a * ‖ξ‖ ^ 2 : ℝ) : ℂ))) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  have hi := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < ((2 * a : ℝ) : ℂ).re by simpa using (mul_pos (by norm_num : (0:ℝ) < 2) ha))
    (0 : ℂ) (0 : Plane)
  have hn := hi.norm
  convert hn using 1
  ext ξ
  simp only [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    Complex.zero_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← Real.exp_nat_mul]
  congr 1
  simp
  ring

lemma abel_integrable (f : L2) {a : ℝ} (ha : 0 < a) (x : Plane) (t : ℝ) :
    Integrable (fun ξ : Plane =>
      Complex.exp (Complex.I * ((inner ℝ x ξ - t * ‖ξ‖ ^ 2 : ℝ) : ℂ) -
        ((a * ‖ξ‖ ^ 2 : ℝ) : ℂ)) * fourier f ξ) volume := by
  have hg := (memLp_gaussian ha).integrable_mul (fourier_memLp f)
  have hc : Continuous (fun ξ : Plane =>
      Complex.exp (Complex.I * ((inner ℝ x ξ - t * ‖ξ‖ ^ 2 : ℝ) : ℂ) -
        ((a * ‖ξ‖ ^ 2 : ℝ) : ℂ))) := by fun_prop
  apply hg.mono (hc.aestronglyMeasurable.mul (fourier_memLp f).aestronglyMeasurable)
  filter_upwards with ξ
  change ‖Complex.exp (Complex.I * ((inner ℝ x ξ - t * ‖ξ‖ ^ 2 : ℝ) : ℂ) -
    ((a * ‖ξ‖ ^ 2 : ℝ) : ℂ)) * fourier f ξ‖ ≤
      ‖Complex.exp (-((a * ‖ξ‖ ^ 2 : ℝ) : ℂ)) * fourier f ξ‖
  simp only [norm_mul, Complex.norm_exp, Complex.sub_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, zero_mul, mul_zero, sub_zero, zero_sub, le_refl]

def evolution (f : L2) (x : Plane) (t : ℝ) : ℂ :=
  (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • ∫ ξ : Plane, phase x t ξ * fourier f ξ

lemma evolution_integrable {f : L2} (hf : Integrable (fourier f) volume)
    (x : Plane) (t : ℝ) :
    Integrable (fun ξ => phase x t ξ * fourier f ξ) volume := by
  apply hf.mono ((continuous_phase x t).aestronglyMeasurable.mul hf.1)
  filter_upwards with ξ
  simp

lemma continuous_evolution {f : L2} (hf : Integrable (fourier f) volume) :
    Continuous (fun z : Plane × ℝ => evolution f z.1 z.2) := by
  have hc : Continuous (fun z : Plane × ℝ =>
      ∫ ξ : Plane, phase z.1 z.2 ξ * fourier f ξ) := by
    apply continuous_of_dominated (bound := fun ξ => ‖fourier f ξ‖)
    · intro z
      exact ((continuous_phase z.1 z.2).aestronglyMeasurable.mul hf.1)
    · intro z
      filter_upwards with ξ
      simp
    · exact hf.norm
    · filter_upwards with ξ
      exact (continuous_phase_parameters ξ).mul continuous_const
  have hm : Continuous (fun z : Plane × ℝ =>
      (((((2 * Real.pi) ^ 2)⁻¹ : ℝ) : ℂ)) *
        ∫ ξ : Plane, phase z.1 z.2 ξ * fourier f ξ) :=
    continuous_const.mul hc
  simpa only [evolution, Complex.real_smul] using hm

def gaussianWeight (a : ℝ) (ξ : Plane) : ℝ := Real.exp (-a * ‖ξ‖ ^ 2)

lemma gaussianWeight_pos (a : ℝ) (ξ : Plane) : 0 < gaussianWeight a ξ := Real.exp_pos _

lemma gaussianWeight_le_one {a : ℝ} (ha : 0 ≤ a) (ξ : Plane) :
    gaussianWeight a ξ ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)

lemma abel_eq_weighted (f : L2) (a : ℝ) (x : Plane) (t : ℝ) :
    abel f a x t = (((2 * Real.pi) ^ 2)⁻¹ : ℝ) •
      ∫ ξ : Plane, phase x t ξ * (gaussianWeight a ξ : ℂ) * fourier f ξ := by
  unfold abel
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [phase, gaussianWeight, sub_eq_add_neg, Complex.exp_add,
    Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]

lemma gaussian_error_integrable {f : L2} (hf : Integrable (fourier f) volume)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun ξ => (1 - gaussianWeight a ξ) * ‖fourier f ξ‖) volume := by
  apply hf.norm.mono
  · exact (by unfold gaussianWeight; fun_prop : Continuous (fun ξ => 1 - gaussianWeight a ξ)).aestronglyMeasurable.mul
      hf.norm.aestronglyMeasurable
  · filter_upwards with ξ
    simpa only [norm_mul, Real.norm_eq_abs, abs_norm,
      abs_of_nonneg (sub_nonneg.mpr (gaussianWeight_le_one ha ξ))] using
        (mul_le_of_le_one_left (norm_nonneg (fourier f ξ))
          (show 1 - gaussianWeight a ξ ≤ 1 by linarith [gaussianWeight_pos a ξ]))

lemma gaussian_error_tendsto_zero {f : L2} (hf : Integrable (fourier f) volume) :
    Tendsto (fun a : ℝ => ∫ ξ : Plane, (1 - gaussianWeight a ξ) * ‖fourier f ξ‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ a := by
    filter_upwards [self_mem_nhdsWithin] with a ha using le_of_lt ha
  have h := tendsto_integral_filter_of_dominated_convergence
    (f := fun _ : Plane => (0 : ℝ)) (fun ξ => ‖fourier f ξ‖)
    (he.mono (fun a ha => (gaussian_error_integrable hf ha).1))
    (he.mono (fun a ha => by
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (sub_nonneg.mpr (gaussianWeight_le_one ha ξ))]
      exact mul_le_of_le_one_left (norm_nonneg (fourier f ξ)) (show 1 - gaussianWeight a ξ ≤ 1 by linarith [gaussianWeight_pos a ξ])))
    hf.norm (by
      filter_upwards with ξ
      have hc : Continuous (fun a : ℝ => (1 - gaussianWeight a ξ) * ‖fourier f ξ‖) := by
        unfold gaussianWeight
        fun_prop
      simpa [gaussianWeight] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [integral_zero] using h

lemma weighted_evolution_integrable {f : L2} (hf : Integrable (fourier f) volume)
    {a : ℝ} (ha : 0 ≤ a) (x : Plane) (t : ℝ) :
    Integrable (fun ξ => phase x t ξ * (gaussianWeight a ξ : ℂ) * fourier f ξ) volume := by
  apply hf.mono
  · have hg : Continuous (fun ξ : Plane => (gaussianWeight a ξ : ℂ)) := by
      unfold gaussianWeight
      fun_prop
    exact ((continuous_phase x t).mul hg).aestronglyMeasurable.mul hf.1
  · filter_upwards with ξ
    simp only [norm_mul, norm_phase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussianWeight_pos a ξ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (gaussianWeight_le_one ha ξ)

lemma norm_abel_sub_evolution_le {f : L2} (hf : Integrable (fourier f) volume)
    {a : ℝ} (ha : 0 ≤ a) (x : Plane) (t : ℝ) :
    ‖abel f a x t - evolution f x t‖ ≤
      ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : Plane, (1 - gaussianWeight a ξ) * ‖fourier f ξ‖ := by
  have hc : 0 ≤ ((2 * Real.pi) ^ 2)⁻¹ := by positivity
  rw [abel_eq_weighted, evolution, ← smul_sub,
    ← integral_sub (weighted_evolution_integrable hf ha x t) (evolution_integrable hf x t),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    _ ≤ ∫ ξ : Plane, ‖phase x t ξ * (gaussianWeight a ξ : ℂ) * fourier f ξ -
        phase x t ξ * fourier f ξ‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ξ
      have he : phase x t ξ * (gaussianWeight a ξ : ℂ) * fourier f ξ -
          phase x t ξ * fourier f ξ =
          phase x t ξ * (((gaussianWeight a ξ - 1 : ℝ) : ℂ)) * fourier f ξ := by
        push_cast
        ring
      rw [he]
      simp only [norm_mul, norm_phase, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (gaussianWeight_le_one ha ξ))]
      ring

lemma abel_tendstoUniformly {f : L2} (hf : Integrable (fourier f) volume) :
    TendstoUniformly (fun a (z : Plane × ℝ) => abel f a z.1 z.2)
      (fun z => evolution f z.1 z.2) (𝓝[>] (0 : ℝ)) := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  have hlim := (gaussian_error_tendsto_zero hf).const_mul (((2 * Real.pi) ^ 2)⁻¹)
  simp only [mul_zero] at hlim
  have he := (tendsto_order.1 hlim).2 ε hε
  filter_upwards [he, self_mem_nhdsWithin] with a ha ha'
  intro z
  rw [dist_comm, dist_eq_norm]
  exact (norm_abel_sub_evolution_le hf (le_of_lt ha') z.1 z.2).trans_lt ha

def AnnularFourierSupport (f : L2) (c₀ C₀ N : ℝ) : Prop :=
  ∀ᵐ ξ : Plane ∂volume, ξ ∉ {ξ | c₀ * N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀ * N} → fourier f ξ = 0

lemma fourier_integrable_of_bounded_support {f : L2} {R : ℝ}
    (hs : ∀ᵐ ξ : Plane ∂volume, R < ‖ξ‖ → fourier f ξ = 0) :
    Integrable (fourier f) volume := by
  have hi := ((fourier_memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0 : Plane) R)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [hs] with ξ hξ hξ'
  apply hξ
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hξ'

lemma AnnularFourierSupport.integrable {f : L2} {c₀ C₀ N : ℝ}
    (hs : AnnularFourierSupport f c₀ C₀ N) : Integrable (fourier f) volume := by
  apply fourier_integrable_of_bounded_support (R := C₀ * N)
  filter_upwards [hs] with ξ hξ hξ'
  apply hξ
  intro h
  exact (not_le.mpr hξ') h.2

def shortTimeLevel (f : L2) (x₀ : Plane) (t₀ s lam : ℝ) : Set Plane :=
  Metric.ball x₀ 1 ∩ {x | ∃ t ∈ Icc t₀ (t₀ + s), lam < ‖evolution f x t‖}

lemma isOpen_timeLevel {f : L2} (hf : Integrable (fourier f) volume)
    (t₀ s lam : ℝ) : IsOpen {x : Plane | ∃ t ∈ Icc t₀ (t₀ + s), lam < ‖evolution f x t‖} := by
  have he : {x : Plane | ∃ t ∈ Icc t₀ (t₀ + s), lam < ‖evolution f x t‖} =
      ⋃ t ∈ Icc t₀ (t₀ + s), {x | lam < ‖evolution f x t‖} := by
    ext x
    simp
  rw [he]
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro _
  apply isOpen_lt continuous_const
  exact ((continuous_evolution hf).comp (continuous_id.prodMk continuous_const)).norm

lemma measurableSet_shortTimeLevel {f : L2} (hf : Integrable (fourier f) volume)
    (x₀ : Plane) (t₀ s lam : ℝ) : MeasurableSet (shortTimeLevel f x₀ t₀ s lam) :=
  Metric.isOpen_ball.measurableSet.inter (isOpen_timeLevel hf t₀ s lam).measurableSet

def ShortTimeWeakEstimate (c₀ C₀ p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (f : L2),
    AnnularFourierSupport f c₀ C₀ ((2 : ℝ) ^ j) →
    ∀ (x₀ : Plane) (t₀ s : ℝ), 0 ≤ s → s ≤ ((2 : ℝ) ^ j)⁻¹ →
    ∀ lam : ℝ, 0 < lam →
    volume (shortTimeLevel f x₀ t₀ s lam) ≤
      ENNReal.ofReal ((C * (((2 : ℝ) ^ j) ^ (1 / 3 : ℝ)) * ‖f‖ / lam) ^ p)

lemma fourier_energy (f : L2) :
    ∫ ξ : Plane, ‖fourier f ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * ‖f‖ ^ 2 := by
  let g := MeasureTheory.Lp.fourierTransformₗᵢ Plane ℂ f
  have hg : ∫ ξ : Plane, ‖g ξ‖ ^ 2 = ‖f‖ ^ 2 := by
    calc
      _ = inner ℝ g g := by simp only [L2.inner_def, real_inner_self_eq_norm_sq]
      _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
      _ = ‖f‖ ^ 2 := by rw [show ‖g‖ = ‖f‖ from LinearIsometryEquiv.norm_map _ _]
  change (∫ ξ : Plane, (fun η : Plane => ‖g η‖ ^ 2) ((2 * Real.pi)⁻¹ • ξ)) = _
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun η : Plane => ‖g η‖ ^ 2)
    (show 0 ≤ 2 * Real.pi by positivity)]
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul]
  rw [hg]

lemma norm_evolution_le_fourierL1 (f : L2) (x : Plane) (t : ℝ) :
    ‖evolution f x t‖ ≤ ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : Plane, ‖fourier f ξ‖ := by
  unfold evolution
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 * Real.pi)^2)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_mul, norm_phase, one_mul] using
    norm_integral_le_integral_norm (fun ξ => phase x t ξ * fourier f ξ)

lemma fourierL1_le_support_energy {f : L2} {R : ℝ}
    (hs : ∀ᵐ ξ : Plane ∂volume, R < ‖ξ‖ → fourier f ξ = 0) :
    (∫ ξ : Plane, ‖fourier f ξ‖) ≤
      (2 * Real.pi) * ‖f‖ * Real.sqrt (volume (Metric.closedBall (0 : Plane) R)).toReal := by
  let b : Plane → ℂ := (Metric.closedBall (0 : Plane) R).indicator (fun _ => 1)
  have hb : MemLp b 2 volume := memLp_indicator_const _ measurableSet_closedBall _
    (Or.inr (isCompact_closedBall (0 : Plane) R).measure_ne_top)
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp (fourier f) (ENNReal.ofReal (2 : ℝ)) volume by simpa using fourier_memLp f)
    (show MemLp b (ENNReal.ofReal (2 : ℝ)) volume by simpa using hb)
  have he : ∫ ξ : Plane, ‖fourier f ξ‖ * ‖b ξ‖ = ∫ ξ : Plane, ‖fourier f ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hs] with ξ hξ
    by_cases hm : ξ ∈ Metric.closedBall (0 : Plane) R
    · simp [b, hm]
    · have hz : fourier f ξ = 0 := hξ (by simpa only [Metric.mem_closedBall,
          dist_zero_right, not_le] using hm)
      simp [hz]
  have hb2 : ∫ ξ : Plane, ‖b ξ‖ ^ (2 : ℝ) =
      (volume (Metric.closedBall (0 : Plane) R)).toReal := by
    calc
      _ = ∫ ξ : Plane, (Metric.closedBall (0 : Plane) R).indicator (fun _ => (1 : ℝ)) ξ := by
        apply integral_congr_ae
        filter_upwards with ξ
        by_cases hm : ξ ∈ Metric.closedBall (0 : Plane) R <;> simp [b, hm]
      _ = _ := by simp [integral_indicator measurableSet_closedBall, measureReal_def]
  rw [he, hb2] at hh
  simp only [Real.rpow_two] at hh
  rw [fourier_energy, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have he2 : Real.sqrt ((2 * Real.pi)^2 * ‖f‖^2) = (2 * Real.pi) * ‖f‖ := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rwa [he2] at hh

lemma sobolevWeight_one_le (ξ : Plane) : 1 ≤ (1 + ‖ξ‖^2) ^ (1 / 3 : ℝ) := by
  exact Real.one_le_rpow (by nlinarith [sq_nonneg ‖ξ‖]) (by norm_num)

lemma sobolev_energy_nonneg (f : L2) :
    0 ≤ ∫ ξ : Plane, (1 + ‖ξ‖^2) ^ (1 / 3 : ℝ) * ‖fourier f ξ‖^2 := by
  apply integral_nonneg
  intro ξ
  positivity

lemma norm_le_hThirdNorm {f : L2} (hf : InHThird f) : ‖f‖ ≤ hThirdNorm f := by
  have hm : ∫ ξ : Plane, ‖fourier f ξ‖^2 ≤
      ∫ ξ : Plane, (1 + ‖ξ‖^2) ^ (1 / 3 : ℝ) * ‖fourier f ξ‖^2 := by
    apply integral_mono ((fourier_memLp f).integrable_norm_pow (by norm_num)) hf
    intro ξ
    exact le_mul_of_one_le_left (sq_nonneg _) (sobolevWeight_one_le ξ)
  rw [fourier_energy] at hm
  have hc : 0 < (2 * Real.pi)^2 := by positivity
  have hm' := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hc.le)
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hm'
  unfold hThirdNorm
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hc.le)
    (sobolev_energy_nonneg f))).mpr hm'

lemma norm_evolution_le_bounded_frequency {f : L2} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ᵐ ξ : Plane ∂volume, R < ‖ξ‖ → fourier f ξ = 0)
    (x : Plane) (t : ℝ) :
    ‖evolution f x t‖ ≤ (Real.sqrt Real.pi / (2 * Real.pi)) * R * ‖f‖ := by
  have hh := (norm_evolution_le_fourierL1 f x t).trans
    (mul_le_mul_of_nonneg_left (fourierL1_le_support_energy hs) (by positivity))
  have hv : Real.sqrt (volume (Metric.closedBall (0 : Plane) R)).toReal =
      R * Real.sqrt Real.pi := by
    rw [EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
      ENNReal.toReal_ofReal Real.pi_pos.le, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR]
  rw [hv] at hh
  have hid : ((2 * Real.pi)^2)⁻¹ * ((2 * Real.pi) * ‖f‖ * (R * Real.sqrt Real.pi)) =
      (Real.sqrt Real.pi / (2 * Real.pi)) * R * ‖f‖ := by
    field_simp
  rwa [hid] at hh

lemma norm_evolution_le_low_frequency {f : L2} (hf : InHThird f)
    (hs : ∀ᵐ ξ : Plane ∂volume, 1 < ‖ξ‖ → fourier f ξ = 0)
    (x : Plane) (t : ℝ) :
    ‖evolution f x t‖ ≤ (Real.sqrt Real.pi / (2 * Real.pi)) * hThirdNorm f := by
  have he := norm_evolution_le_bounded_frequency (by norm_num : (0 : ℝ) ≤ 1) hs x t
  rw [mul_one] at he
  exact he.trans (mul_le_mul_of_nonneg_left (norm_le_hThirdNorm hf) (by positivity))

open FourierTransform

lemma fourier_schwartz_ae (φ : SchwartzMap Plane ℂ) :
    fourier (φ.toLp 2 volume) =ᵐ[volume]
      (fun ξ => (𝓕 φ) ((2 * Real.pi)⁻¹ • ξ)) := by
  have he : (MeasureTheory.Lp.fourierTransformₗᵢ Plane ℂ (φ.toLp 2 volume) : Plane → ℂ) =ᵐ[volume]
      (fun ξ => (𝓕 φ) ξ) := by
    change ((𝓕 (φ.toLp 2 volume) : L2) : Plane → ℂ) =ᵐ[volume] _
    rw [SchwartzMap.toLp_fourier_eq]
    exact (𝓕 φ).coeFn_toLp 2 volume
  exact (Measure.quasiMeasurePreserving_smul volume
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).ae_eq_comp he

lemma fourier_schwartz_integrable (φ : SchwartzMap Plane ℂ) :
    Integrable (fourier (φ.toLp 2 volume)) volume := by
  apply Integrable.congr _ (fourier_schwartz_ae φ).symm
  exact (𝓕 φ).integrable.comp_smul (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))

lemma phase_zero_eq_scaled_inverse_character (x ξ : Plane) :
    phase x 0 ξ = Complex.exp (((2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ • ξ) x : ℝ) : ℂ)
      * Complex.I) := by
  simp only [phase, zero_mul, sub_zero, real_inner_smul_left, real_inner_comm ξ x]
  congr 1
  have hc : 2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ ξ x) = inner ℝ ξ x := by
    field_simp
  rw [hc, mul_comm]

lemma evolution_schwartz_zero (φ : SchwartzMap Plane ℂ) (x : Plane) :
    evolution (φ.toLp 2 volume) x 0 = φ x := by
  let q : Plane → ℂ := fun η =>
    Complex.exp (((2 * Real.pi * inner ℝ η x : ℝ) : ℂ) * Complex.I) * (𝓕 φ) η
  have he : ∫ ξ : Plane, phase x 0 ξ * fourier (φ.toLp 2 volume) ξ =
      ∫ ξ : Plane, q ((2 * Real.pi)⁻¹ • ξ) := by
    apply integral_congr_ae
    filter_upwards [fourier_schwartz_ae φ] with ξ hξ
    rw [hξ, phase_zero_eq_scaled_inverse_character]
  unfold evolution
  rw [he, Measure.integral_comp_inv_smul_of_nonneg volume q (by positivity : 0 ≤ 2 * Real.pi)]
  have hconst : (2 * Real.pi)^2 ≠ 0 := by positivity
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ hconst, one_smul]
  have hfi : ∫ η : Plane, q η = (𝓕⁻ ((𝓕 φ : SchwartzMap Plane ℂ) : Plane → ℂ)) x := by
    rw [Real.fourierInv_eq']
    simp only [q, smul_eq_mul]
  change (∫ η : Plane, q η) = _
  rw [hfi, ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]

lemma closedBall_ae_eq_ball (x : Plane) (r : ℝ) :
    Metric.closedBall x r =ᵐ[volume] Metric.ball x r := by
  exact (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
    (le_of_eq (Measure.addHaar_closedBall_eq_addHaar_ball volume x r))
    measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm

lemma diskAverage_eq_average (f : L2) (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    diskAverage f x r = ⨍ y in Metric.closedBall x r, f y := by
  rw [setAverage_congr (closedBall_ae_eq_ball x r), setAverage_eq]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_nonneg]
  rw [mul_comm (r ^ 2) Real.pi]
  rfl

lemma diskNormAverage_eq_average (f : Plane → ℂ) (x : Plane) (z : ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    (Real.pi * r ^ 2)⁻¹ * (∫ y in Metric.ball x r, ‖f y - z‖) =
      ⨍ y in Metric.closedBall x r, ‖f y - z‖ := by
  rw [setAverage_congr (closedBall_ae_eq_ball x r), setAverage_eq]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_nonneg,
    smul_eq_mul]
  rw [mul_comm (r ^ 2) Real.pi]

lemma ae_isLebesguePoint (f : L2) : ∀ᵐ x : Plane ∂volume, IsLebesguePoint f x := by
  have hf := (Lp.memLp f).locallyIntegrable (by norm_num)
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hf 1] with x hx
  refine ⟨f x, ?_⟩
  have hc : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul, Metric.mem_closedBall, dist_self] using (le_of_lt hr)
  have ht := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hc
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (diskNormAverage_eq_average f x (f x) (le_of_lt hr)).symm

lemma ae_diskAverage_tendsto (f : L2) : ∀ᵐ x : Plane ∂volume,
    Tendsto (diskAverage f x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hf := (Lp.memLp f).locallyIntegrable (by norm_num)
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 1] with x hx
  have hc : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul, Metric.mem_closedBall, dist_self] using (le_of_lt hr)
  have ht := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hc
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (diskAverage_eq_average f x (le_of_lt hr)).symm

lemma lebesgueRepresentative_ae (f : L2) : lebesgueRepresentative f =ᵐ[volume] f := by
  filter_upwards [ae_diskAverage_tendsto f] with x hx
  exact hx.limUnder_eq

end PlanarEndpoint

namespace PlanarEndpoint

def sobolevWeight (ξ : Plane) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (1 / 3 : ℝ)
def sobolevMeasure : Measure Plane := volume.withDensity (fun ξ => ENNReal.ofReal (sobolevWeight ξ))

lemma continuous_sobolevWeight : Continuous sobolevWeight := by
  unfold sobolevWeight
  fun_prop (disch := norm_num)

lemma sobolevWeight_pos (ξ : Plane) : 0 < sobolevWeight ξ := by
  exact lt_of_lt_of_le zero_lt_one (sobolevWeight_one_le ξ)

instance sobolevMeasure_locallyFinite : IsLocallyFiniteMeasure sobolevMeasure :=
  IsLocallyFiniteMeasure.withDensity_ofReal continuous_sobolevWeight

lemma integrable_sq_sobolevMeasure_iff (g : Plane → ℂ) :
    Integrable (fun ξ => ‖g ξ‖ ^ 2) sobolevMeasure ↔
      Integrable (fun ξ => sobolevWeight ξ * ‖g ξ‖ ^ 2) volume := by
  rw [sobolevMeasure, integrable_withDensity_iff_integrable_smul'
    (continuous_sobolevWeight.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sobolevWeight_pos _).le, smul_eq_mul]

lemma integral_sq_sobolevMeasure (g : Plane → ℂ) :
    (∫ ξ, ‖g ξ‖ ^ 2 ∂sobolevMeasure) =
      ∫ ξ, sobolevWeight ξ * ‖g ξ‖ ^ 2 := by
  rw [sobolevMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_sobolevWeight.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sobolevWeight_pos _).le, smul_eq_mul]

lemma fourier_memLp_sobolev {f : L2} (hf : InHThird f) :
    MemLp (fourier f) 2 sobolevMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    ((fourier_memLp f).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _))).2
  exact (integrable_sq_sobolevMeasure_iff _).2 hf

lemma fourier_sub_ae (f g : L2) :
    fourier (f - g) =ᵐ[volume] fun ξ => fourier f ξ - fourier g ξ := by
  have he := Lp.coeFn_sub (Lp.fourierTransformₗᵢ Plane ℂ f) (Lp.fourierTransformₗᵢ Plane ℂ g)
  rw [← (Lp.fourierTransformₗᵢ Plane ℂ).map_sub] at he
  exact (Measure.quasiMeasurePreserving_smul volume
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).ae_eq_comp he

lemma hThirdNorm_eq_weighted_eLpNorm {f : L2} (hf : InHThird f) :
    hThirdNorm f = (2 * Real.pi)⁻¹ * (eLpNorm (fourier f) 2 sobolevMeasure).toReal := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (fourier_memLp_sobolev hf)]
  have he (y : ℝ) : y ^ ((2 : ℝ)⁻¹) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, he,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), integral_sq_sobolevMeasure]
  unfold hThirdNorm sobolevWeight
  rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq (by positivity)]

lemma exists_smooth_compact_fourier_approx {f : L2} (hf : InHThird f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Plane → ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (fun ξ => fourier f ξ - g ξ) 2 sobolevMeasure ≤ ENNReal.ofReal ε := by
  exact MemLp.exist_eLpNorm_sub_le (by norm_num) (by norm_num)
    (fourier_memLp_sobolev hf) hε

end PlanarEndpoint

namespace PlanarEndpoint
open FourierTransform

lemma inHThird_of_fourier_memLp_sobolev {f : L2}
    (hf : MemLp (fourier f) 2 sobolevMeasure) : InHThird f :=
  (integrable_sq_sobolevMeasure_iff _).1
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf)

def frequencyDilation : Plane ≃L[ℝ] Plane :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 * Real.pi)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero))

@[simp] lemma frequencyDilation_apply (ξ : Plane) :
    frequencyDilation ξ = (2 * Real.pi) • ξ := rfl

def inverseCompactFourier (g : Plane → ℂ) (hc : HasCompactSupport g)
    (hd : ContDiff ℝ ∞ g) : SchwartzMap Plane ℂ :=
  𝓕⁻ ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequencyDilation)
    (hc.toSchwartzMap hd))

lemma fourier_inverseCompactFourier_ae (g : Plane → ℂ) (hc : HasCompactSupport g)
    (hd : ContDiff ℝ ∞ g) :
    fourier ((inverseCompactFourier g hc hd).toLp 2) =ᵐ[volume] g := by
  refine (fourier_schwartz_ae _).trans (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only [inverseCompactFourier, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    frequencyDilation_apply, smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul]
  rfl

lemma exists_schwartz_hThird_approx {f : L2} (hf : InHThird f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SchwartzMap Plane ℂ, InHThird (φ.toLp 2 volume) ∧
      InHThird (f - φ.toLp 2 volume) ∧ hThirdNorm (f - φ.toLp 2 volume) ≤ ε := by
  have hc : 0 < 2 * Real.pi := by positivity
  obtain ⟨g, hgcompact, hgsmooth, hgap⟩ :=
    exists_smooth_compact_fourier_approx hf (mul_pos hc hε)
  let φ := inverseCompactFourier g hgcompact hgsmooth
  have hφ : fourier (φ.toLp 2 volume) =ᵐ[volume] g :=
    fourier_inverseCompactFourier_ae g hgcompact hgsmooth
  have hφw : fourier (φ.toLp 2 volume) =ᵐ[sobolevMeasure] g :=
    (withDensity_absolutelyContinuous _ _).ae_le hφ
  have hgw : MemLp g 2 sobolevMeasure :=
    hgsmooth.continuous.memLp_of_hasCompactSupport hgcompact
  have hφmem : MemLp (fourier (φ.toLp 2 volume)) 2 sobolevMeasure :=
    (memLp_congr_ae hφw).2 hgw
  have hsub : fourier (f - φ.toLp 2 volume) =ᵐ[volume] fun ξ => fourier f ξ - g ξ := by
    filter_upwards [fourier_sub_ae f (φ.toLp 2 volume), hφ] with ξ hξ hφξ
    rw [hξ, hφξ]
  have hsubw : fourier (f - φ.toLp 2 volume) =ᵐ[sobolevMeasure] fun ξ => fourier f ξ - g ξ :=
    (withDensity_absolutelyContinuous _ _).ae_le hsub
  have hsubmem : MemLp (fourier (f - φ.toLp 2 volume)) 2 sobolevMeasure :=
    (memLp_congr_ae hsubw).2 ((fourier_memLp_sobolev hf).sub hgw)
  have hH := inHThird_of_fourier_memLp_sobolev hsubmem
  refine ⟨φ, inHThird_of_fourier_memLp_sobolev hφmem, hH, ?_⟩
  rw [hThirdNorm_eq_weighted_eLpNorm hH, eLpNorm_congr_ae hsubw]
  have hgap' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgap
  rw [ENNReal.toReal_ofReal (mul_pos hc hε).le] at hgap'
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ε) :=
      mul_le_mul_of_nonneg_left hgap' (inv_nonneg.mpr hc.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

end PlanarEndpoint

namespace PlanarEndpoint

lemma gaussian_fourier_norm_integrable (f : L2) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ => gaussianWeight a ξ * ‖fourier f ξ‖) volume := by
  have hh := ((memLp_gaussian ha).integrable_mul (fourier_memLp f)).norm
  convert hh using 1
  ext ξ
  simp only [Pi.mul_apply, gaussianWeight, norm_mul, Complex.norm_exp, Complex.neg_re,
    Complex.ofReal_re, neg_mul]

lemma continuousAt_abel_parameters (f : L2) (z : ℝ × Plane × ℝ) (hz : 0 < z.1) :
    ContinuousAt (fun w : ℝ × Plane × ℝ => abel f w.1 w.2.1 w.2.2) z := by
  let F : (ℝ × Plane × ℝ) → Plane → ℂ := fun w ξ =>
    phase w.2.1 w.2.2 ξ * (gaussianWeight w.1 ξ : ℂ) * fourier f ξ
  have hm (w : ℝ × Plane × ℝ) : AEStronglyMeasurable (F w) volume := by
    exact (((continuous_phase w.2.1 w.2.2).mul (by
      unfold gaussianWeight
      fun_prop)).aestronglyMeasurable).mul (fourier_memLp f).aestronglyMeasurable
  have hnear : ∀ᶠ w : ℝ × Plane × ℝ in 𝓝 z, z.1 / 2 < w.1 :=
    (continuous_fst.tendsto z).eventually (Ioi_mem_nhds (half_lt_self hz))
  have hc : ContinuousAt (fun w => ∫ ξ, F w ξ) z := by
    apply continuousAt_of_dominated (bound := fun ξ => gaussianWeight (z.1 / 2) ξ * ‖fourier f ξ‖)
    · exact Filter.Eventually.of_forall hm
    · filter_upwards [hnear] with w hw
      filter_upwards with ξ
      simp only [F, norm_mul, norm_phase, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (gaussianWeight_pos _ _)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hw.le) (sq_nonneg _)
    · exact gaussian_fourier_norm_integrable f (half_pos hz)
    · filter_upwards with ξ
      apply Continuous.continuousAt
      dsimp [F, phase, gaussianWeight]
      fun_prop
  have ha : (fun w : ℝ × Plane × ℝ => abel f w.1 w.2.1 w.2.2) =
      fun w => (((2 * Real.pi)^2)⁻¹ : ℝ) • ∫ ξ, F w ξ := by
    funext w
    exact abel_eq_weighted f w.1 w.2.1 w.2.2
  rw [ha]
  have hconst : ContinuousAt (fun _ : ℝ × Plane × ℝ => (((2 * Real.pi)^2)⁻¹ : ℝ)) z :=
    continuousAt_const
  exact hconst.smul hc

lemma continuousOn_abel_parameters (f : L2) :
    ContinuousOn (fun w : ℝ × Plane × ℝ => abel f w.1 w.2.1 w.2.2) {w | 0 < w.1} := by
  intro z hz
  exact (continuousAt_abel_parameters f z hz).continuousWithinAt

end PlanarEndpoint

namespace PlanarEndpoint

def evolutionMultiplier (t : ℝ) (η : Plane) : ℂ :=
  phase 0 t ((2 * Real.pi) • η)

@[simp] lemma norm_evolutionMultiplier (t : ℝ) (η : Plane) :
    ‖evolutionMultiplier t η‖ = 1 := norm_phase _ _ _

lemma continuous_evolutionMultiplier (t : ℝ) : Continuous (evolutionMultiplier t) := by
  unfold evolutionMultiplier phase
  fun_prop

lemma memLp_evolutionFourier (f : L2) (t : ℝ) :
    MemLp (fun η => evolutionMultiplier t η * (Lp.fourierTransformₗᵢ Plane ℂ f) η)
      2 volume := by
  apply (Lp.memLp (Lp.fourierTransformₗᵢ Plane ℂ f)).mono
    ((continuous_evolutionMultiplier t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
  filter_upwards with η
  simp

def l2Evolution (f : L2) (t : ℝ) : L2 :=
  (Lp.fourierTransformₗᵢ Plane ℂ).symm
    ((memLp_evolutionFourier f t).toLp
      (fun η => evolutionMultiplier t η * (Lp.fourierTransformₗᵢ Plane ℂ f) η))

lemma l2Evolution_fourier_ae (f : L2) (t : ℝ) :
    (Lp.fourierTransformₗᵢ Plane ℂ (l2Evolution f t) : Plane → ℂ) =ᵐ[volume]
      fun η => evolutionMultiplier t η * (Lp.fourierTransformₗᵢ Plane ℂ f) η := by
  simp only [l2Evolution, LinearIsometryEquiv.apply_symm_apply]
  exact (memLp_evolutionFourier f t).coeFn_toLp

lemma fourier_l2Evolution_ae (f : L2) (t : ℝ) :
    fourier (l2Evolution f t) =ᵐ[volume] fun ξ => phase 0 t ξ * fourier f ξ := by
  have h := (Measure.quasiMeasurePreserving_smul volume (r := (2 * Real.pi)⁻¹)
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).ae_eq_comp
      (l2Evolution_fourier_ae f t)
  filter_upwards [h] with ξ hξ
  simpa only [fourier, evolutionMultiplier, Function.comp_apply, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul] using hξ

lemma norm_l2Evolution (f : L2) (t : ℝ) : ‖l2Evolution f t‖ = ‖f‖ := by
  rw [l2Evolution, LinearIsometryEquiv.norm_map, Lp.norm_toLp]
  calc
    _ = (eLpNorm (Lp.fourierTransformₗᵢ Plane ℂ f) 2 volume).toReal := by
      congr 1
      apply eLpNorm_congr_norm_ae (memLp_evolutionFourier f t).aestronglyMeasurable
        (Lp.aestronglyMeasurable _)
      filter_upwards with η
      simp
    _ = ‖Lp.fourierTransformₗᵢ Plane ℂ f‖ := (Lp.norm_def _).symm
    _ = ‖f‖ := (Lp.fourierTransformₗᵢ Plane ℂ).norm_map f

lemma l2Evolution_zero (f : L2) : l2Evolution f 0 = f := by
  apply (Lp.fourierTransformₗᵢ Plane ℂ).injective
  apply Lp.ext
  filter_upwards [l2Evolution_fourier_ae f 0] with η hη
  simpa [evolutionMultiplier, phase] using hη

lemma l2Evolution_sub (f g : L2) (t : ℝ) :
    l2Evolution (f - g) t = l2Evolution f t - l2Evolution g t := by
  apply (Lp.fourierTransformₗᵢ Plane ℂ).injective
  rw [map_sub]
  apply Lp.ext
  have hs : (Lp.fourierTransformₗᵢ Plane ℂ (f - g) : Plane → ℂ) =ᵐ[volume]
      fun η => (Lp.fourierTransformₗᵢ Plane ℂ f) η -
        (Lp.fourierTransformₗᵢ Plane ℂ g) η := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [l2Evolution_fourier_ae (f - g) t,
    l2Evolution_fourier_ae f t, l2Evolution_fourier_ae g t,
    hs, Lp.coeFn_sub (Lp.fourierTransformₗᵢ Plane ℂ (l2Evolution f t))
      (Lp.fourierTransformₗᵢ Plane ℂ (l2Evolution g t))] with η hfg hf hg hs hsub
  rw [hfg, hs, hsub]
  simp only [Pi.sub_apply, hf, hg, mul_sub]

lemma dist_l2Evolution (f g : L2) (t : ℝ) :
    dist (l2Evolution f t) (l2Evolution g t) = dist f g := by
  rw [dist_eq_norm, ← l2Evolution_sub, norm_l2Evolution, dist_eq_norm]

lemma inHThird_l2Evolution {f : L2} (hf : InHThird f) (t : ℝ) :
    InHThird (l2Evolution f t) := by
  apply (show InHThird f from hf).congr
  filter_upwards [fourier_l2Evolution_ae f t] with ξ hξ
  simp [hξ]

lemma hThirdNorm_l2Evolution (f : L2) (t : ℝ) :
    hThirdNorm (l2Evolution f t) = hThirdNorm f := by
  unfold hThirdNorm
  congr 2
  apply integral_congr_ae
  filter_upwards [fourier_l2Evolution_ae f t] with ξ hξ
  simp [hξ]

end PlanarEndpoint

namespace PlanarEndpoint
open FourierTransform
open scoped SchwartzMap

lemma inverse_fourier_continuous {g : Plane → ℂ} (hg : Integrable g volume) :
    Continuous (𝓕⁻ g) := by
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner.neg hg

lemma inverse_fourier_pairing {g h : Plane → ℂ}
    (hg : Integrable g volume) (hh : Integrable h volume) :
    (∫ x, (𝓕⁻ g) x * h x) = ∫ ξ, g ξ * (𝓕⁻ h) ξ := by
  have hsym : (-innerₗ Plane).flip = -innerₗ Plane := by
    ext x y
    change -(inner ℝ y x) = -(inner ℝ x y)
    rw [real_inner_comm y x]
  have hp := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ Plane) Real.continuous_fourierChar continuous_inner.neg hg hh
  rw [hsym] at hp
  exact hp

lemma l2_inverse_fourier_ae (g : L2) (hg : Integrable (g : Plane → ℂ) volume) :
    ((Lp.fourierTransformₗᵢ Plane ℂ).symm g : Plane → ℂ) =ᵐ[volume]
      𝓕⁻ (g : Plane → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    ((inverse_fourier_continuous hg).locallyIntegrable)
  intro q hqd hqc
  have hcc : HasCompactSupport (fun x => (q x : ℂ)) :=
    hqc.comp_left (show (fun r : ℝ => (r : ℂ)) 0 = 0 by simp)
  have hcd : ContDiff ℝ ∞ (fun x => (q x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hqd
  let φ : SchwartzMap Plane ℂ := hcc.toSchwartzMap hcd
  have hdist := congrArg (fun T : 𝓢'(Plane, ℂ) => T φ)
    (Lp.fourierInv_toTemperedDistribution_eq g)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hdist
  have hp := inverse_fourier_pairing hg φ.integrable
  have hφ : (fun x => φ x) = fun x => (q x : ℂ) := rfl
  calc
    (∫ x, q x • ((Lp.fourierTransformₗᵢ Plane ℂ).symm g) x) =
        ∫ x, φ x * ((Lp.fourierTransformₗᵢ Plane ℂ).symm g) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [hφ, Complex.real_smul]
    _ = ∫ ξ, (𝓕⁻ φ) ξ * g ξ := hdist.symm
    _ = ∫ ξ, g ξ * (𝓕⁻ (φ : Plane → ℂ)) ξ := by
      simp only [← SchwartzMap.fourierInv_coe, mul_comm]
    _ = ∫ x, (𝓕⁻ (g : Plane → ℂ)) x * φ x := hp.symm
    _ = ∫ x, q x • (𝓕⁻ (g : Plane → ℂ)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [hφ, Complex.real_smul, mul_comm]

  all_goals rfl

end PlanarEndpoint

namespace PlanarEndpoint
open FourierTransform

lemma integrable_mathlib_fourier {f : L2} (hf : Integrable (fourier f) volume) :
    Integrable (fun η => (Lp.fourierTransformₗᵢ Plane ℂ f) η) volume := by
  have hi := hf.comp_smul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  simpa only [fourier, smul_smul, inv_mul_cancel₀ (mul_ne_zero
    (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul] using hi

lemma integrable_evolutionFourier {f : L2} (hf : Integrable (fourier f) volume)
    (t : ℝ) : Integrable (fun η => evolutionMultiplier t η *
      (Lp.fourierTransformₗᵢ Plane ℂ f) η) volume := by
  have hi := integrable_mathlib_fourier hf
  apply hi.mono ((continuous_evolutionMultiplier t).aestronglyMeasurable.mul hi.1)
  filter_upwards [] with η
  simp

lemma evolution_eq_mathlib_inverse (f : L2) (x : Plane) (t : ℝ) :
    evolution f x t = (𝓕⁻ (fun η => evolutionMultiplier t η *
      (Lp.fourierTransformₗᵢ Plane ℂ f) η)) x := by
  let q : Plane → ℂ := fun η =>
    Complex.exp (((2 * Real.pi * inner ℝ η x : ℝ) : ℂ) * Complex.I) *
      (evolutionMultiplier t η * (Lp.fourierTransformₗᵢ Plane ℂ f) η)
  have he : ∫ ξ : Plane, phase x t ξ * fourier f ξ =
      ∫ ξ : Plane, q ((2 * Real.pi)⁻¹ • ξ) := by
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [q]
    rw [← phase_zero_eq_scaled_inverse_character]
    simp only [evolutionMultiplier, smul_smul, mul_inv_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul,
      ← mul_assoc]
    change phase x t ξ * fourier f ξ = (phase x 0 ξ * phase 0 t ξ) * fourier f ξ
    congr 1
    simp only [phase, inner_zero_left, zero_mul, sub_zero, zero_sub, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold evolution
  rw [he, Measure.integral_comp_inv_smul_of_nonneg volume q
    (by positivity : 0 ≤ 2 * Real.pi)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi)^2 ≠ 0), one_smul]
  rw [Real.fourierInv_eq']
  rfl

lemma l2Evolution_ae_evolution {f : L2} (hf : Integrable (fourier f) volume) (t : ℝ) :
    (l2Evolution f t : Plane → ℂ) =ᵐ[volume] (fun x => evolution f x t) := by
  let g : L2 := (memLp_evolutionFourier f t).toLp _
  have hg := (memLp_evolutionFourier f t).coeFn_toLp
  have hi : Integrable (g : Plane → ℂ) volume :=
    (integrable_evolutionFourier hf t).congr hg.symm
  have ha := l2_inverse_fourier_ae g hi
  filter_upwards [ha] with x hx
  change ((Lp.fourierTransformₗᵢ Plane ℂ).symm g) x = _
  rw [hx, Real.fourierInv_congr_ae hg, evolution_eq_mathlib_inverse]

abbrev Time := ↥(Set.Icc (0 : ℝ) 1)
abbrev TimePath := C(Time, ℂ)

lemma continuous_evolution_time (f : L2) (hf : Integrable (fourier f) volume)
    (x : Plane) : Continuous (fun t : Time => evolution f x (t : ℝ)) := by
  have ht : Continuous (fun t : Time => (x, (t : ℝ))) :=
    continuous_const.prodMk continuous_subtype_val
  have hh := (continuous_evolution (f := f) hf).comp ht
  simpa only [Function.comp_def] using hh

def evolutionPath (f : L2) (hf : Integrable (fourier f) volume) (x : Plane) : TimePath :=
  ⟨fun t : Time => evolution f x (t : ℝ), continuous_evolution_time f hf x⟩

lemma continuous_evolutionPath (f : L2) (hf : Integrable (fourier f) volume) :
    Continuous (evolutionPath f hf) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have ht : Continuous (fun z : Plane × Time => (z.1, (z.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hh := (continuous_evolution (f := f) hf).comp ht
  simpa only [Function.comp_def, Function.uncurry_def, evolutionPath, ContinuousMap.coe_mk] using hh

end PlanarEndpoint

namespace PlanarEndpoint

lemma mainConclusion_of_fourier_integrable (f : L2)
    (hf : Integrable (fourier f) volume) : MainConclusion f := by
  have hzero : ∀ᵐ x : Plane ∂volume, evolution f x 0 = f x := by
    have h := l2Evolution_ae_evolution (f := f) hf 0
    rw [l2Evolution_zero] at h
    exact h.symm
  let E : Set Plane := {x | IsLebesguePoint f x ∧
    Tendsto (diskAverage f x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) ∧
    lebesgueRepresentative f x = f x ∧ evolution f x 0 = f x}
  have hE : volume Eᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [ae_isLebesguePoint f, ae_diskAverage_tendsto f,
      lebesgueRepresentative_ae f, hzero] with x h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄⟩
  refine ⟨E, hE, ?_⟩
  intro x hx
  obtain ⟨hl, hd, hr, hz⟩ := hx
  have ht : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
  have hhh := (continuous_evolution (f := f) hf).comp ht
  have hc : Continuous (evolution f x) := by
    simpa only [Function.comp_def] using hhh
  have hu := (abel_tendstoUniformly (f := f) hf).comp (fun t : ℝ => (x, t))
  refine ⟨hl, evolution f x, hc.continuousOn, hz.trans hr.symm, ?_, ?_, ?_, ?_⟩
  · simpa only [hz] using hd
  · intro t _
    exact hu.tendsto_at t
  · rw [hr, ← hz]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact hu.tendstoUniformlyOn

end PlanarEndpoint
end

end OAI
