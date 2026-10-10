import OAI.Analysis.Littlewood.Model

namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem integral_schwartz_mul_gaussian
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) (c : ℂ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 +
      2 * Real.pi * c * (x : ℂ))) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + Complex.I * c) ^ 2) := by
  have hG : Integrable (fun x : ℝ ↦
      Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 + 2 * Real.pi * c * (x : ℂ))) := by
    have hp : 0 < ((Real.pi : ℂ) * b).re := by
      simpa using mul_pos Real.pi_pos hb
    simpa only [neg_mul, add_zero] using
      integrable_cexp_quadratic hp (2 * Real.pi * c) 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner
    (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable hG
  have heq : (∫ x : ℝ, (𝓕 (𝓕⁻ f : 𝓢(ℝ, ℂ))) x *
      Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 + 2 * Real.pi * c * (x : ℂ))) =
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        (𝓕 (fun x : ℝ ↦ Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 +
          2 * Real.pi * c * (x : ℂ)))) ξ := by
    simpa only [flip_innerₗ, smul_eq_mul] using! h
  rw [FourierTransform.fourier_fourierInv_eq] at heq
  rw [heq, fourier_gaussian_pi' hb c]
  simp_rw [← mul_assoc, mul_comm ((𝓕⁻ f : 𝓢(ℝ, ℂ)) _) (1 / b ^ (1 / 2 : ℂ)), mul_assoc]
  exact integral_const_mul _ _

/-- The damping kernel has modulus at most one on the closed right half-plane. -/
theorem norm_damped_quadratic_le_one {b : ℂ} (hb : 0 ≤ b.re) (u x : ℝ) :
    ‖Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x).re = -Real.pi * b.re * x ^ 2 := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hb) (sq_nonneg _)

/-- The Fourier-side Gaussian also has modulus at most one. -/
theorem norm_damped_fourier_le_one {b : ℂ} (hb : 0 ≤ b.re) (y : ℝ) :
    ‖Complex.exp (-Real.pi / b * (y : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-Real.pi / b * (y : ℂ) ^ 2).re =
      -Real.pi * (b.re / Complex.normSq b) * y ^ 2 := by
    simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im, pow_two,
      Complex.inv_re]
  rw [hre]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le)
      (div_nonneg hb (Complex.normSq_nonneg _))) (sq_nonneg _)

theorem integral_schwartz_mul_gaussian_boundary
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 ≤ b.re) (hb0 : b ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2) := by
  let bn : ℕ → ℂ := fun n ↦ b + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hbn (n : ℕ) : 0 < (bn n).re := by
    dsimp [bn]
    simpa using add_pos_of_nonneg_of_pos hb (by positivity : 0 < 1 / ((n : ℝ) + 1))
  have hbnlim : Filter.Tendsto bn Filter.atTop (𝓝 b) := by
    have hz := Complex.continuous_ofReal.tendsto 0 |>.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [bn] using tendsto_const_nhds.add hz
  have hblim : b ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases h : b.im = 0
    · left
      have hr : b.re ≠ 0 := by
        intro hr
        exact hb0 (Complex.ext hr h)
      exact lt_of_le_of_ne hb (Ne.symm hr)
    · exact Or.inr h
  have hcpow : Filter.Tendsto (fun n ↦ 1 / (bn n) ^ (1 / 2 : ℂ))
      Filter.atTop (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    exact tendsto_const_nhds.div
      (continuousAt_cpow_const hblim |>.tendsto.comp hbnlim)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hb0))
  have hl : Filter.Tendsto
      (fun n ↦ ∫ x : ℝ, f x * Complex.exp (-Real.pi * bn n * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x)) Filter.atTop
      (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x))) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact f.integrable.norm
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_damped_quadratic_le_one (hbn n).le u x)
    · filter_upwards with x
      exact tendsto_const_nhds.mul
        (Complex.continuous_exp.tendsto _ |>.comp
          (((tendsto_const_nhds.mul hbnlim).mul tendsto_const_nhds).sub
            tendsto_const_nhds))
  have hr : Filter.Tendsto
      (fun n ↦ ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / bn n * ((ξ : ℂ) + u) ^ 2)) Filter.atTop
      (𝓝 (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2))) := by
    apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable.norm
    · intro n
      filter_upwards with ξ
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      simpa only [Complex.ofReal_add] using norm_damped_fourier_le_one (hbn n).le (ξ + u)
    · filter_upwards with ξ
      exact tendsto_const_nhds.mul
        (Complex.continuous_exp.tendsto _ |>.comp
          ((tendsto_const_nhds.div hbnlim hb0).mul tendsto_const_nhds))
  have heq (n : ℕ) :
      (∫ x : ℝ, f x * Complex.exp (-Real.pi * bn n * (x : ℂ) ^ 2 -
        2 * Real.pi * Complex.I * u * x)) =
      1 / (bn n) ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
        Complex.exp (-Real.pi / bn n * ((ξ : ℂ) + u) ^ 2) := by
    convert integral_schwartz_mul_gaussian f (hbn n) (-Complex.I * u) using 1 <;>
      simp [← mul_assoc, sub_eq_add_neg]
  exact tendsto_nhds_unique hl ((hcpow.mul hr).congr' (Filter.Eventually.of_forall (fun n ↦ (heq n).symm)))

def realPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

@[simp] theorem norm_realPhase (x : ℝ) : ‖realPhase x‖ = 1 := by
  simp [realPhase, Complex.norm_exp, Complex.mul_re]

/-- Multiplication by a continuous real phase preserves integrability. -/
theorem integrable_schwartz_phase (f : 𝓢(ℝ, ℂ)) (p : ℝ → ℝ)
    (hp : Continuous p) : Integrable (fun x ↦ f x * realPhase (p x)) := by
  apply f.integrable.norm.mono'
  · apply Continuous.aestronglyMeasurable
    unfold realPhase
    exact f.continuous.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hp)))
  · filter_upwards with x
    simp

/-- Quadratic Fourier identity with an undamped, nonzero real curvature. -/
theorem integral_schwartz_quadratic_exact (f : 𝓢(ℝ, ℂ))
    {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
    1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-Real.pi / t * (ξ + u) ^ 2) := by
  have hb0 : -Complex.I * (t : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht)
  have hb : 0 ≤ (-Complex.I * (t : ℂ)).re := by simp
  convert integral_schwartz_mul_gaussian_boundary f hb hb0 u using 1
  · apply integral_congr_ae
    filter_upwards with x
    congr 1
    unfold realPhase
    congr 1
    push_cast
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    congr 1
    unfold realPhase
    congr 1
    push_cast
    field_simp
    simp [Complex.I_sq]
    ring

/-- Fourier inversion specialized to the linear factor in the quadratic formula. -/
theorem integral_schwartz_inverse_linear (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-2 * Real.pi * ξ * x)) = f x := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) ↦ g x)
    (show (𝓕 (𝓕⁻ f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from
      FourierTransform.fourier_fourierInv_eq f)
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul, realPhase, mul_comm]

/-- The remaining quadratic Fourier multiplier differs from one by at most
π ξ² / |t|, uniformly in the stationary point. -/
theorem norm_quadratic_multiplier_sub_one {t : ℝ} (ξ : ℝ) :
    ‖realPhase (-Real.pi / t * ξ ^ 2) - 1‖ ≤ Real.pi / |t| * ξ ^ 2 := by
  calc
    _ ≤ ‖-Real.pi / t * ξ ^ 2‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_nonneg (sq_nonneg ξ)]

@[simp] theorem realPhase_add (x y : ℝ) :
    realPhase (x + y) = realPhase x * realPhase y := by
  simp [realPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem uniform_quadratic_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ Real.pi / |t| * (∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) ∧
      (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
        (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
          realPhase (-Real.pi / t * u ^ 2)) * (f (u / t) + E) := by
  let p : ℝ → ℝ := fun ξ ↦ -2 * Real.pi * ξ * (u / t)
  let q : ℝ → ℝ := fun ξ ↦ -Real.pi / t * ξ ^ 2
  let d : ℝ → ℂ := fun ξ ↦ (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ) * (realPhase (q ξ) - 1)
  have hp : Continuous p := by unfold p; fun_prop
  have hq : Continuous q := by unfold q; fun_prop
  have hl := integrable_schwartz_phase (𝓕⁻ f : 𝓢(ℝ, ℂ)) p hp
  have ht' := integrable_schwartz_phase (𝓕⁻ f : 𝓢(ℝ, ℂ)) (fun ξ ↦ p ξ + q ξ) (hp.add hq)
  have hd : Integrable d := by
    convert ht'.sub hl using 1
    ext ξ
    simp only [d, realPhase_add, Pi.sub_apply]
    ring
  refine ⟨∫ ξ, d ξ, ?_, ?_⟩
  · have hm : Integrable (fun ξ : ℝ ↦ ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) := by
      have h : Integrable (fun ξ : ℝ ↦ ‖ξ‖ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) :=
        (𝓕⁻ f : 𝓢(ℝ, ℂ)).integrable_pow_mul volume 2
      simpa only [Real.norm_eq_abs, sq_abs] using h
    calc
      ‖∫ ξ, d ξ‖ ≤ ∫ ξ, ‖d ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : ℝ, (Real.pi / |t|) * (ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) := by
        apply integral_mono hd.norm (hm.const_mul _)
        intro ξ
        simp only [d, norm_mul, norm_realPhase, mul_one]
        calc
          _ ≤ ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖ * (Real.pi / |t| * ξ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_quadratic_multiplier_sub_one ξ) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  · have hlin : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ)) = f (u / t) :=
      integral_schwartz_inverse_linear f (u / t)
    have hsum : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ + q ξ)) =
        f (u / t) + ∫ ξ, d ξ := by
      rw [← hlin, ← integral_add hl hd]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [d, realPhase_add]
      ring
    have hphase (ξ : ℝ) :
        realPhase (-Real.pi / t * (ξ + u) ^ 2) =
          realPhase (-Real.pi / t * u ^ 2) * realPhase (p ξ + q ξ) := by
      rw [← realPhase_add]
      congr 1
      dsimp [p, q]
      ring
    rw [integral_schwartz_quadratic_exact f ht u]
    simp_rw [hphase]
    have hi : (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
          (realPhase (-Real.pi / t * u ^ 2) * realPhase (p ξ + q ξ))) =
        realPhase (-Real.pi / t * u ^ 2) *
          (∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (p ξ + q ξ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      ring
    rw [hi, hsum]
    ring

/-- The prefactor in uniform quadratic integration has precisely the required
modulus. No pointwise lower estimate for a Littlewood polynomial is involved. -/
theorem norm_quadratic_prefactor (t u : ℝ) :
    ‖1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
        realPhase (-Real.pi / t * u ^ 2)‖ = 1 / Real.sqrt |t| := by
  rw [norm_mul, norm_realPhase, mul_one, norm_div, norm_one]
  congr 1
  have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hexp, Complex.norm_cpow_real]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact (Real.sqrt_eq_rpow _).symm

/-- The argument of the nonzero imaginary curvature, on the principal branch. -/
theorem arg_negative_imaginary {t : ℝ} (ht : t ≠ 0) :
    Complex.arg (-Complex.I * (t : ℂ)) = -Real.sign t * Real.pi / 2 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have heq : -Complex.I * (t : ℂ) = Complex.I * ((-t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.arg_mul_real (neg_pos.mpr ht), Complex.arg_I,
      Real.sign_of_neg ht]
    ring
  · rw [Complex.arg_mul_real ht, Complex.arg_neg_I, Real.sign_of_pos ht]
    ring

theorem quadratic_prefactor_eq {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ)) *
        realPhase (-Real.pi / t * u ^ 2) =
      realPhase (Real.pi * Real.sign t / 4 - Real.pi * u ^ 2 / t) /
        (Real.sqrt |t| : ℂ) := by
  have he : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by norm_num
  rw [one_div, ← Complex.cpow_neg, he, Complex.cpow_ofReal]
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg (abs_nonneg t), ← Real.sqrt_eq_rpow, arg_negative_imaginary ht]
  have harg : (-Real.sign t * Real.pi / 2) * (-(1 / 2)) =
      Real.pi * Real.sign t / 4 := by ring
  rw [harg]
  have hphase (x : ℝ) : (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I = realPhase x := by
    unfold realPhase
    rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hphase]
  rw [mul_assoc, ← realPhase_add]
  have heq : Real.pi * Real.sign t / 4 + -Real.pi / t * u ^ 2 =
      Real.pi * Real.sign t / 4 - Real.pi * u ^ 2 / t := by ring
  rw [heq]
  push_cast
  ring

theorem uniform_quadratic_integration (g : ℝ → ℂ) (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {β : ℝ} (hβ : β ≠ 0) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ (Real.pi / |β| * (∫ ξ : ℝ, ξ ^ 2 *
        ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ, ℂ)) ξ‖)) / T ∧
      (∫ x : ℝ, g x * realPhase (2 * Real.pi * (T * β * x ^ 2 / 2 - u * x))) =
        (realPhase (2 * Real.pi * (Real.sign β / 8 - u ^ 2 / (2 * T * β))) /
          (Real.sqrt (T * |β|) : ℂ)) * (g (u / (T * β)) + E) := by
  obtain ⟨E, hE, hEq⟩ := uniform_quadratic_error (hg.toSchwartzMap hgs)
    (mul_ne_zero hT.ne' hβ) u
  refine ⟨E, ?_, ?_⟩
  · convert hE using 1
    rw [abs_mul, abs_of_pos hT]
    ring
  · rw [quadratic_prefactor_eq (mul_ne_zero hT.ne' hβ)] at hEq
    have hs : Real.sign (T * β) = Real.sign β := by
      rcases lt_or_gt_of_ne hβ with hβ | hβ
      · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hT hβ), Real.sign_of_neg hβ]
      · rw [Real.sign_of_pos (mul_pos hT hβ), Real.sign_of_pos hβ]
    have hnorm : |T * β| = T * |β| := by rw [abs_mul, abs_of_pos hT]
    simp only [hs, hnorm, HasCompactSupport.toSchwartzMap] at hEq
    convert hEq using 1
    · apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    · congr 2
      congr 1
      ring

end
end AsymptoticallyMinimalLittlewood

end OAI
