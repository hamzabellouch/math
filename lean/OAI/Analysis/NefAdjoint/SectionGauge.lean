import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace NefAdjoint.SectionGauge

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem first_holder {m : ℝ} (hm : 1 < m)
    {F A : X → ℝ≥0∞} (hF : AEMeasurable F μ) (hA : AEMeasurable A μ) :
    (∫⁻ x, F x ^ (1 / m) * A x ^ ((m - 1) / m) ∂μ) ^ m ≤
      (∫⁻ x, F x ∂μ) * (∫⁻ x, A x ∂μ) ^ (m - 1) := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hm1 : 0 < m - 1 := sub_pos.mpr hm
  have hsum : 1 / m + (m - 1) / m = 1 := by
    field_simp
    ring
  have hh := ENNReal.lintegral_mul_norm_pow_le hF hA
    (le_of_lt (one_div_pos.mpr hm0)) (le_of_lt (div_pos hm1 hm0)) hsum
  have hpow := ENNReal.monotone_rpow_of_nonneg hm0.le hh
  calc
    _ ≤ ((∫⁻ x, F x ∂μ) ^ (1 / m) *
        (∫⁻ x, A x ∂μ) ^ ((m - 1) / m)) ^ m := hpow
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hm0.le,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [one_div_mul_cancel hm0.ne', div_mul_cancel₀ _ hm0.ne', ENNReal.rpow_one]

theorem mixture_bound {m d : ℝ} (hm : 1 < m) (hd : 0 ≤ d) (hdm : d ≤ m - 1)
    {ρ σ : X → ℝ≥0∞} (hρ : AEMeasurable ρ μ) (hσ : AEMeasurable σ μ)
    (hnorm : ∫⁻ x, ρ x ∂μ = 1) :
    (∫⁻ x, ρ x ^ (1 - d / (m - 1)) *
      (max (ρ x) (σ x)) ^ (d / (m - 1)) ∂μ) ^ (m - 1) ≤
      (1 + ∫⁻ x, σ x ∂μ) ^ d := by
  have hm1 : 0 < m - 1 := sub_pos.mpr hm
  have hη0 : 0 ≤ d / (m - 1) := div_nonneg hd hm1.le
  have hη1 : d / (m - 1) ≤ 1 := (div_le_one hm1).mpr hdm
  have hmax : (∫⁻ x, max (ρ x) (σ x) ∂μ) ≤ 1 + ∫⁻ x, σ x ∂μ := by
    calc
      _ ≤ ∫⁻ x, ρ x + σ x ∂μ := lintegral_mono fun x => max_le (le_add_right le_rfl)
        (le_add_left le_rfl)
      _ = _ := by rw [lintegral_add_left' hρ, hnorm]
  have hh := ENNReal.lintegral_mul_norm_pow_le hρ (hρ.max hσ)
    (sub_nonneg.mpr hη1) hη0 (sub_add_cancel 1 (d / (m - 1)))
  rw [hnorm, ENNReal.one_rpow, one_mul] at hh
  have hbound := hh.trans (ENNReal.monotone_rpow_of_nonneg hη0 hmax)
  calc
    _ ≤ ((1 + ∫⁻ x, σ x ∂μ) ^ (d / (m - 1))) ^ (m - 1) :=
      ENNReal.monotone_rpow_of_nonneg hm1.le hbound
    _ = _ := by
      rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ hm1.ne']

theorem two_holder_bound {m d : ℝ} (hm : 1 < m) (hd : 0 ≤ d) (hdm : d ≤ m - 1)
    {F ρ σ : X → ℝ≥0∞} (hF : AEMeasurable F μ)
    (hρ : AEMeasurable ρ μ) (hσ : AEMeasurable σ μ)
    (hnorm : ∫⁻ x, ρ x ∂μ = 1) :
    (∫⁻ x, F x ^ (1 / m) *
      (ρ x ^ (1 - d / (m - 1)) *
        (max (ρ x) (σ x)) ^ (d / (m - 1))) ^ ((m - 1) / m) ∂μ) ^ m ≤
      (∫⁻ x, F x ∂μ) * (1 + ∫⁻ x, σ x ∂μ) ^ d := by
  exact (first_holder hm hF
    ((hρ.pow_const _).mul ((hρ.max hσ).pow_const _))).trans
      (mul_le_mul_right (mixture_bound hm hd hdm hρ hσ hnorm) _)

def expDensity (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp t)

lemma expDensity_add (s t : ℝ) :
    expDensity (s + t) = expDensity s * expDensity t := by
  simp [expDensity, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos s).le]

lemma expDensity_mul (s t : ℝ) :
    expDensity (s * t) = expDensity s ^ t := by
  rw [expDensity, expDensity, Real.exp_mul,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos s)]

lemma expDensity_mono : Monotone expDensity := by
  intro x y h
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)

lemma expDensity_max (s t : ℝ) :
    expDensity (max s t) = max (expDensity s) (expDensity t) := by
  rcases le_total s t with h | h
  · rw [max_eq_right h, max_eq_right (expDensity_mono h)]
  · rw [max_eq_left h, max_eq_left (expDensity_mono h)]

lemma aemeasurable_expDensity {u : X → ℝ} (hu : AEMeasurable u μ) :
    AEMeasurable (fun x => expDensity (u x)) μ := hu.exp.ennreal_ofReal

def sourceG (m d τ φ a b : ℝ) : ℝ :=
  (m - 1) * τ + a / m + b + d * max 0 (φ + a / m - τ)

theorem canonical_density_mixture (m d τ φ a b : ℝ)
    (hm : m ≠ 0) (hm1 : m - 1 ≠ 0) :
    (sourceG m d τ φ a b - a - m * b) / (m - 1) =
      (1 - d / (m - 1)) * (τ - a / m - b) +
      (d / (m - 1)) * (max (τ - a / m) φ - b) := by
  unfold sourceG
  by_cases h : τ - a / m ≤ φ
  · rw [max_eq_right h, max_eq_right (show (0 : ℝ) ≤ φ + a / m - τ by linarith)]
    field_simp
    ring
  · rw [max_eq_left (le_of_not_ge h),
      max_eq_left (show φ + a / m - τ ≤ (0 : ℝ) by linarith)]
    field_simp
    ring

theorem exponential_density_mixture (m d τ φ a b : ℝ)
    (hm : m ≠ 0) (hm1 : m - 1 ≠ 0) :
    expDensity ((sourceG m d τ φ a b - a - m * b) / (m - 1)) =
      expDensity (τ - a / m - b) ^ (1 - d / (m - 1)) *
      (max (expDensity (τ - a / m - b)) (expDensity (φ - b))) ^ (d / (m - 1)) := by
  rw [canonical_density_mixture m d τ φ a b hm hm1, expDensity_add]
  rw [mul_comm (1 - d / (m - 1)), mul_comm (d / (m - 1))]
  rw [expDensity_mul, expDensity_mul, ← max_sub_sub_right, expDensity_max]

lemma real_gauge_factorization (m v G a b : ℝ) (hm : 1 < m) (hv : 0 ≤ v) :
    (v ^ 2 * Real.exp (-G)) ^ (1 / m) *
      (Real.exp ((G - a - m * b) / (m - 1))) ^ ((m - 1) / m) =
      v ^ (2 / m) * Real.exp (-a / m - b) := by
  have hm0 : m ≠ 0 := ne_of_gt (lt_trans zero_lt_one hm)
  have hm1 : m - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  rw [Real.mul_rpow (sq_nonneg v) (Real.exp_pos (-G)).le,
    ← Real.rpow_natCast v 2, ← Real.rpow_mul hv]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (1 / m) = 2 / m by ring,
    ← Real.exp_mul, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

lemma gauge_factorization (m v G a b : ℝ) (hm : 1 < m) (hv : 0 ≤ v) :
    ENNReal.ofReal (v ^ (2 / m) * Real.exp (-a / m - b)) =
      ENNReal.ofReal (v ^ 2 * Real.exp (-G)) ^ (1 / m) *
      expDensity ((G - a - m * b) / (m - 1)) ^ ((m - 1) / m) := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hF : 0 ≤ v ^ 2 * Real.exp (-G) := mul_nonneg (sq_nonneg v) (Real.exp_pos _).le
  rw [expDensity, ENNReal.ofReal_rpow_of_nonneg hF (one_div_nonneg.mpr hm0.le),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hF _)]
  exact congrArg ENNReal.ofReal (real_gauge_factorization m v G a b hm hv).symm

theorem source_gauge_bound {m d : ℝ} (hm : 1 < m) (hd : 0 ≤ d) (hdm : d ≤ m - 1)
    {w : X → ℂ} {τ φ a b : X → ℝ}
    (hw : AEMeasurable w μ) (hτ : AEMeasurable τ μ) (hφ : AEMeasurable φ μ)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hnorm : ∫⁻ x, expDensity (τ x - a x / m - b x) ∂μ = 1) :
    (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ (2 / m) * Real.exp (-a x / m - b x)) ∂μ) ^ m ≤
      (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 *
        Real.exp (-sourceG m d (τ x) (φ x) (a x) (b x))) ∂μ) *
      (1 + ∫⁻ x, expDensity (φ x - b x) ∂μ) ^ d := by
  have hm0 : m ≠ 0 := ne_of_gt (lt_trans zero_lt_one hm)
  have hm1 : m - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  have hG : AEMeasurable (fun x => sourceG m d (τ x) (φ x) (a x) (b x)) μ :=
    (((hτ.const_mul (m - 1)).add (ha.div_const m)).add hb).add
      ((aemeasurable_const.max ((hφ.add (ha.div_const m)).sub hτ)).const_mul d)
  have hF := ((hw.norm.pow_const (2 : ℕ)).mul hG.neg.exp).ennreal_ofReal
  have hρ := aemeasurable_expDensity ((hτ.sub (ha.div_const m)).sub hb)
  have hσ := aemeasurable_expDensity (hφ.sub hb)
  calc
    _ = (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 *
          Real.exp (-sourceG m d (τ x) (φ x) (a x) (b x))) ^ (1 / m) *
        (expDensity (τ x - a x / m - b x) ^ (1 - d / (m - 1)) *
          (max (expDensity (τ x - a x / m - b x))
            (expDensity (φ x - b x))) ^ (d / (m - 1))) ^ ((m - 1) / m) ∂μ) ^ m := by
      congr 1
      apply lintegral_congr
      intro x
      rw [gauge_factorization m ‖w x‖ _ _ _ hm (norm_nonneg _),
        exponential_density_mixture m d (τ x) (φ x) (a x) (b x) hm0 hm1]
    _ ≤ _ := two_holder_bound hm hd hdm hF hρ hσ hnorm

theorem tail_mass_tendsto_zero {u : ℕ → X → ℝ} {uLim φ b bound : X → ℝ}
    {C R : ℝ} (hR : C < R)
    (hu : ∀ n, Measurable (u n)) (hφ : Measurable φ) (hb : Measurable b)
    (hbound : Integrable bound μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, Real.exp (u n x - b x) ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (uLim x)))
    (hcompare : ∀ᵐ x ∂μ, uLim x ≤ φ x + C) :
    Tendsto (fun n => ∫ x in {x | φ x - u n x < -R}, Real.exp (u n x - b x) ∂μ)
      atTop (𝓝 0) := by
  classical
  let A : ℕ → Set X := fun n => {x | φ x - u n x < -R}
  let f : ℕ → X → ℝ := fun n => (A n).indicator (fun x => Real.exp (u n x - b x))
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_lt (hφ.sub (hu n)) measurable_const
  have hf (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    (((hu n).sub hb).exp.indicator (hA n)).aestronglyMeasurable
  have hf_bound (n : ℕ) : ∀ᵐ x ∂μ, ‖f n x‖ ≤ bound x := by
    filter_upwards [hdom n] with x hx
    by_cases hax : x ∈ A n
    · simpa [f, Set.indicator_of_mem hax, Real.norm_of_nonneg (Real.exp_pos _).le] using hx
    · simp only [f, Set.indicator_of_notMem hax, norm_zero]
      exact (Real.exp_pos _).le.trans hx
  have hf_lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim, hcompare] with x hx hcx
    have hxR : uLim x < φ x + R := by linarith
    have hsmall : ∀ᶠ n in atTop, u n x < φ x + R := hx.eventually_lt_const hxR
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with n hn
    have hax : x ∉ A n := by
      dsimp [A]
      linarith
    simp [f, Set.indicator_of_notMem hax]
  have ht := tendsto_integral_of_dominated_convergence bound hf hbound hf_bound hf_lim
  simpa only [f, integral_indicator (hA _), integral_zero] using ht

theorem eventually_gauge_lt_one {q m ε : ℕ → ℝ} {K : ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hm : ∀ n, 0 ≤ m n)
    (hestimate : ∀ n, q n ^ m n ≤ K * ε n) :
    ∀ᶠ n in atTop, q n < 1 := by
  have hlim : Tendsto (fun n => K * ε n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hε
  filter_upwards [hlim.eventually_lt_const zero_lt_one] with n hn
  by_contra hq
  have hq' : 1 ≤ q n := le_of_not_gt hq
  have hp : (1 : ℝ) ≤ q n ^ m n := by
    simpa using Real.rpow_le_rpow zero_le_one hq' (hm n)
  exact (not_le_of_gt ((hestimate n).trans_lt hn)) hp

section Extremal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalize_gauge {Q : E → ℝ} {k : ℝ} (hk : 0 < k)
    (hhom : ∀ (r : ℝ), 0 < r → ∀ v, Q (r • v) = r ^ k * Q v)
    {v : E} (hv : 0 < Q v) :
    Q ((Q v) ^ (-1 / k) • v) = 1 := by
  rw [hhom _ (Real.rpow_pos_of_pos hv _) v, ← Real.rpow_mul hv.le]
  rw [div_mul_cancel₀ _ hk.ne', Real.rpow_neg_one, inv_mul_cancel₀ hv.ne']

theorem isCompact_unit_gauge [FiniteDimensional ℝ E]
    {Q : E → ℝ} {k : ℝ} (hk : 0 < k) (hQ : Continuous Q)
    (hzero : Q 0 = 0) (hpos : ∀ v : E, v ≠ 0 → 0 < Q v)
    (hhom : ∀ (r : ℝ), 0 < r → ∀ v, Q (r • v) = r ^ k * Q v) :
    IsCompact {v : E | Q v = 1} := by
  let T : E → E := fun v => (Q v) ^ (-1 / k) • v
  have nonzero_on_sphere {v : E} (hv : v ∈ Metric.sphere (0 : E) 1) : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hT : ContinuousOn T (Metric.sphere (0 : E) 1) := by
    exact (hQ.continuousOn.rpow_const (fun v hv =>
      Or.inl (hpos v (nonzero_on_sphere hv)).ne')).smul continuous_id.continuousOn
  have himage : T '' Metric.sphere (0 : E) 1 = {v : E | Q v = 1} := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact normalize_gauge hk hhom (hpos w (nonzero_on_sphere hw))
    · intro hv
      have hqv : Q v = 1 := hv
      have hv0 : v ≠ 0 := by
        rintro rfl
        norm_num [hzero] at hqv
      have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
      · simp [norm_smul,
          Real.norm_of_nonneg (inv_pos.mpr hr).le, hr.ne']
      · dsimp [T]
        rw [hhom _ (inv_pos.mpr hr), hqv, mul_one,
          ← Real.rpow_mul (inv_pos.mpr hr).le]
        have he : k * (-1 / k) = (-1 : ℝ) := by field_simp
        rw [he, Real.rpow_neg_one, inv_inv, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [← himage]
  exact (isCompact_sphere (0 : E) 1).image_of_continuousOn hT

theorem exists_extremal [FiniteDimensional ℝ E]
    {Q : E → ℝ} {k : ℝ} (hk : 0 < k) (hQ : Continuous Q)
    (hzero : Q 0 = 0) (hpos : ∀ v : E, v ≠ 0 → 0 < Q v)
    (hhom : ∀ (r : ℝ), 0 < r → ∀ v, Q (r • v) = r ^ k * Q v)
    (evaluation : E →L[ℝ] F) (hne : ∃ v, evaluation v ≠ 0) :
    ∃ s : E, Q s = 1 ∧ evaluation s ≠ 0 ∧
      ∀ v : E, Q v = 1 → ‖evaluation v‖ ≤ ‖evaluation s‖ := by
  obtain ⟨v, hv⟩ := hne
  have hv0 : v ≠ 0 := by
    intro h
    exact hv (by simp [h])
  have hqv : 0 < Q v := hpos v hv0
  let r := (Q v) ^ (-1 / k)
  have hr : 0 < r := Real.rpow_pos_of_pos hqv _
  have hrQ : Q (r • v) = 1 := normalize_gauge hk hhom hqv
  have hrv : 0 < ‖evaluation (r • v)‖ := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_pos hr (norm_pos_iff.mpr hv)
  obtain ⟨s, hs, hmax⟩ := (isCompact_unit_gauge hk hQ hzero hpos hhom).exists_isMaxOn
    ⟨r • v, hrQ⟩ evaluation.continuous.norm.continuousOn
  refine ⟨s, hs, ?_, fun v hv => hmax hv⟩
  exact norm_pos_iff.mp (hrv.trans_le (hmax hrQ))

theorem no_smaller_competitor {Q : E → ℝ} {k : ℝ} (hk : 0 < k)
    (hhom : ∀ (r : ℝ), 0 < r → ∀ v, Q (r • v) = r ^ k * Q v)
    (evaluation : E →L[ℝ] F) {s w : E}
    (hs : evaluation s ≠ 0)
    (hmax : ∀ v, Q v = 1 → ‖evaluation v‖ ≤ ‖evaluation s‖)
    (hvalue : evaluation w = evaluation s)
    (hqpos : 0 < Q w) (hqlt : Q w < 1) : False := by
  let r := (Q w) ^ (-1 / k)
  have hr1 : 1 < r := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hqpos hqlt
    (div_neg_of_neg_of_pos (by norm_num) hk)
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hrQ : Q (r • w) = 1 := normalize_gauge hk hhom hqpos
  have hcontra := hmax (r • w) hrQ
  rw [map_smul, norm_smul, Real.norm_of_nonneg hr0.le, hvalue] at hcontra
  have heval : 0 < ‖evaluation s‖ := norm_pos_iff.mpr hs
  nlinarith

end Extremal
end NefAdjoint.SectionGauge

end

end OAI
