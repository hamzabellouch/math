import OAI.Probability.FreeIsing.Posterior.GaussianEnergy

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

omit [Nonempty S] in
lemma covariance_eq_centered_sum_entropy (energy signal a b : S → ℝ) (t : ℝ) :
    mean energy signal (fun s => a s * b s) t -
      mean energy signal a t * mean energy signal b t =
      ∑ s, (a s - mean energy signal a t) * b s * mass energy signal t s := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, ← mean_eq_sum_mass]
  rw [mean_eq_sum_mass energy signal (fun s => a s * b s) t]
  simp only [mul_assoc]

theorem abs_covariance_le_spin_variance_entropy (energy signal a b : S → ℝ) (t : ℝ)
    (ha : ∀ s, a s = -1 ∨ a s = 1)
    (han : ∃ s, a s = -1) (hap : ∃ s, a s = 1)
    (hb : ∀ s, |b s| ≤ 1) :
    |mean energy signal (fun s => a s * b s) t -
      mean energy signal a t * mean energy signal b t| ≤
      1 - mean energy signal a t ^ 2 := by
  let m := mean energy signal a t
  have hm := spin_mean_mem_Ioo energy signal a t ha han hap
  have habs (s : S) : |a s - m| = 1 - a s * m := by
    rcases ha s with hs | hs
    · rw [hs, abs_of_neg (by dsimp [m]; linarith [hm.1])]
      ring
    · rw [hs, abs_of_pos (by dsimp [m]; linarith [hm.2])]
      ring
  rw [covariance_eq_centered_sum_entropy]
  calc
    |∑ s, (a s - mean energy signal a t) * b s * mass energy signal t s| ≤
        ∑ s, |(a s - m) * b s * mass energy signal t s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, (1 - a s * m) * mass energy signal t s := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_mul, abs_of_pos (mass_pos energy signal t s)]
      calc
        |a s - m| * |b s| * mass energy signal t s ≤
            |a s - m| * 1 * mass energy signal t s := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hb s) (abs_nonneg _))
                (mass_pos energy signal t s).le
        _ = _ := by rw [habs]; ring
    _ = 1 - mean energy signal a t ^ 2 := by
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib, sum_mass]
      have heq (s : S) : a s * m * mass energy signal t s =
          m * (a s * mass energy signal t s) := by ring
      simp_rw [heq]
      rw [← Finset.mul_sum, ← mean_eq_sum_mass]
      dsimp [m]
      ring

theorem abs_tiltResponse_le_one_entropy (energy signal observable : S → ℝ) (t : ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |signal s| ≤ 1) :
    |tiltResponse energy signal observable t| ≤ 1 := by
  have hden := spin_mean_variance_pos energy signal observable t hspin hneg hpos
  rw [tiltResponse, abs_div, abs_of_pos hden, div_le_one hden]
  exact abs_covariance_le_spin_variance_entropy energy signal observable signal t
    hspin hneg hpos hsignal

variable {V : Type*} [Fintype V]

def fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) : ℝ :=
  -Real.log (1 - fieldMean energy spin observable x ^ 2)

def fieldEntropyGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * fieldMean energy spin observable x * normalizedFieldCovariance energy spin observable x v

def fieldEntropyHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * (1 + fieldMean energy spin observable x ^ 2) *
      normalizedFieldCovariance energy spin observable x v ^ 2 -
    4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x *
      normalizedFieldCovariance energy spin observable x v

lemma fieldVariance_pos_entropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    0 < 1 - fieldMean energy spin observable x ^ 2 := by
  have h := fieldMean_spin_mem_Ioo energy spin observable x hspin hneg hpos
  nlinarith [h.1, h.2]

theorem abs_normalizedFieldCovariance_le_one_entropy (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |spin s v| ≤ 1) :
    |normalizedFieldCovariance energy spin observable x v| ≤ 1 := by
  rw [← tiltResponse_fieldEnergy_zero]
  exact abs_tiltResponse_le_one_entropy _ _ _ _ hspin hneg hpos hsignal

theorem continuous_normalizedFieldCovariance_entropy (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => normalizedFieldCovariance energy spin observable x v) := by
  exact (continuous_fieldCovariance energy spin observable v).div
    (continuous_const.sub ((continuous_fieldMean energy spin observable).pow 2))
    (fun x => (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).ne')

theorem continuous_fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fieldEntropy energy spin observable) := by
  exact ((continuous_const.sub ((continuous_fieldMean energy spin observable).pow 2)).log
    (fun x => (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).ne')).neg

theorem hasFDerivAt_fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasFDerivAt (fieldEntropy energy spin observable)
      (∑ v, fieldEntropyGradient energy spin observable x v •
        (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x := by
  have hden := (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).ne'
  have hd := ((((hasFDerivAt_fieldMean energy spin observable x).pow 2).const_sub 1).log hden).neg
  change HasFDerivAt (fieldEntropy energy spin observable) _ x at hd
  apply hd.congr_fderiv
  ext y
  simp only [fieldMeanDerivative, fieldEntropyGradient, normalizedFieldCovariance,
    Nat.reduceSub, pow_one, neg_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Finset.mul_sum]
  ring_nf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem continuous_fieldEntropyGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => fieldEntropyGradient energy spin observable x v) :=
  ((continuous_fieldMean energy spin observable).const_mul 2).mul
    (continuous_normalizedFieldCovariance_entropy energy spin observable v hspin hneg hpos)

theorem continuous_fieldEntropyHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    Continuous (fun x => fieldEntropyHessianDiagonal energy spin observable x v) := by
  have hm := continuous_fieldMean energy spin observable
  have hc := continuous_normalizedFieldCovariance_entropy energy spin observable v hspin hneg hpos
  exact (((continuous_const.add (hm.pow 2)).const_mul 2).mul (hc.pow 2)).sub
    ((((hm.const_mul 4).mul (continuous_fieldMean energy spin (fun s => spin s v))).mul hc))

theorem abs_fieldEntropyGradient_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |spin s v| ≤ 1) :
    |fieldEntropyGradient energy spin observable x v| ≤ 2 := by
  have hm := abs_fieldMean_le energy spin observable x 1
    (fun s => (abs_spin_eq_one observable hspin s).le)
  have hc := abs_normalizedFieldCovariance_le_one_entropy energy spin observable x v
    hspin hneg hpos hsignal
  unfold fieldEntropyGradient
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |fieldMean energy spin observable x| * |normalizedFieldCovariance energy spin observable x v|
        ≤ 2 * 1 * 1 := by gcongr
    _ = 2 := by ring

theorem abs_fieldEntropyHessianDiagonal_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s, |spin s v| ≤ 1) :
    |fieldEntropyHessianDiagonal energy spin observable x v| ≤ 8 := by
  have hm := abs_fieldMean_le energy spin observable x 1
    (fun s => (abs_spin_eq_one observable hspin s).le)
  have hn := abs_fieldMean_le energy spin (fun s => spin s v) x 1 hsignal
  have hc := abs_normalizedFieldCovariance_le_one_entropy energy spin observable x v
    hspin hneg hpos hsignal
  have hm2 : fieldMean energy spin observable x ^ 2 ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one _).mpr hm
  have hc2 : normalizedFieldCovariance energy spin observable x v ^ 2 ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one _).mpr hc
  unfold fieldEntropyHessianDiagonal
  calc
    _ ≤ |2 * (1 + fieldMean energy spin observable x ^ 2) *
        normalizedFieldCovariance energy spin observable x v ^ 2| +
        |4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x *
          normalizedFieldCovariance energy spin observable x v| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (2 * (1 + fieldMean energy spin observable x ^ 2) * normalizedFieldCovariance energy spin observable x v ^ 2) (-(4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x * normalizedFieldCovariance energy spin observable x v))
    _ ≤ 2 * (1 + 1) * 1 + 4 * 1 * 1 * 1 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + fieldMean energy spin observable x ^ 2) *
        normalizedFieldCovariance energy spin observable x v ^ 2)]
      simp only [abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      gcongr
    _ = 8 := by ring

section

variable [DecidableEq V]

omit [Nonempty S] in
lemma normalizedFieldCovariance_coordinate_tilt_entropy (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ) :
    normalizedFieldCovariance energy spin observable (fun u => x u + if u = v then t else 0) v =
      tiltResponse (fieldEnergy energy spin x) (fun s => spin s v) observable t := by
  simp only [normalizedFieldCovariance, fieldCovariance_coordinate_tilt,
    fieldMean_coordinate_tilt, tiltResponse]

theorem hasDerivAt_fieldEntropyGradient_coordinate (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (fun r => fieldEntropyGradient energy spin observable
        (fun u => x u + if u = v then r else 0) v)
      (fieldEntropyHessianDiagonal energy spin observable
        (fun u => x u + if u = v then t else 0) v) t := by
  have hd := ((hasDerivAt_mean_covariance (fieldEnergy energy spin x)
    (fun s => spin s v) observable t).const_mul 2).mul
      (hasDerivAt_tiltResponse (fieldEnergy energy spin x) (fun s => spin s v)
        observable t hcoord hspin hneg hpos)
  simp only [fieldEntropyGradient, fieldEntropyHessianDiagonal,
    fieldMean_coordinate_tilt, normalizedFieldCovariance_coordinate_tilt_entropy]
  change HasDerivAt (fun r => 2 * mean (fieldEnergy energy spin x)
    (fun s => spin s v) observable r *
      tiltResponse (fieldEnergy energy spin x) (fun s => spin s v) observable r) _ t at hd
  apply hd.congr_deriv
  have hden := (spin_mean_variance_pos (fieldEnergy energy spin x)
    (fun s => spin s v) observable t hspin hneg hpos).ne'
  unfold tiltResponse
  field_simp [hden]
  ring

theorem hasDerivAt_fieldEntropyGradient_update (energy : S → ℝ)
    (spin : S → V → ℝ) (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (fun r => fieldEntropyGradient energy spin observable (Function.update x v r) v)
      (fieldEntropyHessianDiagonal energy spin observable (Function.update x v t) v) t := by
  simpa only [← update_eq_zero_shift] using
    hasDerivAt_fieldEntropyGradient_coordinate energy spin observable
      (Function.update x v 0) v t hcoord hspin hneg hpos

end

omit [Nonempty S] in
theorem fieldEntropy_generator_identity (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    (∑ v, fieldEntropyGradient energy spin observable x v *
      fieldMean energy spin (fun s => spin s v) x) +
      (1 / 2 : ℝ) * ∑ v, fieldEntropyHessianDiagonal energy spin observable x v =
    (1 + fieldMean energy spin observable x ^ 2) *
      ∑ v, normalizedFieldCovariance energy spin observable x v ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  unfold fieldEntropyGradient fieldEntropyHessianDiagonal
  ring

theorem fieldEntropy_eq_log_cosh (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    fieldEntropy energy spin observable x =
      2 * Real.log (Real.cosh (fieldField energy spin observable x)) := by
  have hm := fieldMean_spin_mem_Ioo energy spin observable x hspin hneg hpos
  have hden := fieldVariance_pos_entropy energy spin observable x hspin hneg hpos
  unfold fieldEntropy fieldField
  rw [Real.cosh_artanh hm, Real.log_div one_ne_zero (Real.sqrt_ne_zero'.mpr hden),
    Real.log_one, Real.log_sqrt hden.le]
  ring

theorem fieldEntropy_nonneg (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    0 ≤ fieldEntropy energy spin observable x := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos
    (fieldVariance_pos_entropy energy spin observable x hspin hneg hpos).le
    (sub_le_self _ (sq_nonneg _))

theorem fieldEntropy_le_abs_field (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    fieldEntropy energy spin observable x ≤ 2 * |fieldField energy spin observable x| := by
  rw [fieldEntropy_eq_log_cosh energy spin observable x hspin hneg hpos]
  have hcosh (z : ℝ) : Real.cosh z ≤ Real.exp |z| := by
    rw [Real.cosh_eq]
    have hp := Real.exp_le_exp.mpr (le_abs_self z)
    have hn := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  have hlog := Real.log_le_log (Real.cosh_pos (fieldField energy spin observable x))
    (hcosh (fieldField energy spin observable x))
  rw [Real.log_exp] at hlog
  linarith

theorem norm_fderiv_fieldEntropy_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) :
    ‖fderiv ℝ (fieldEntropy energy spin observable) x‖ ≤ (Fintype.card V : ℝ) * 2 := by
  rw [(hasFDerivAt_fieldEntropy energy spin observable x hspin hneg hpos).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc
    ‖∑ v, fieldEntropyGradient energy spin observable x v * y v‖ ≤
        ∑ v, ‖fieldEntropyGradient energy spin observable x v * y v‖ := norm_sum_le _ _
    _ ≤ ∑ _v : V, 2 * ‖y‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Real.norm_eq_abs (fieldEntropyGradient energy spin observable x v)]
      exact mul_le_mul
        (abs_fieldEntropyGradient_le energy spin observable x v hspin hneg hpos (fun s => hsignal s v))
        (norm_le_pi_norm y v) (norm_nonneg _) (by norm_num)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

theorem lipschitzWith_fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) :
    LipschitzWith ((Fintype.card V : ℝ≥0) * 2) (fieldEntropy energy spin observable) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hasFDerivAt_fieldEntropy energy spin observable x hspin hneg hpos).differentiableAt)
  intro x
  exact_mod_cast norm_fderiv_fieldEntropy_le energy spin observable x hspin hneg hpos hsignal

open MeasureTheory

theorem integrable_fieldEntropy_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1)
    (hsignal : ∀ s v, |spin s v| ≤ 1) {X : Ω → V → ℝ} (hX : Integrable X μ) :
    Integrable (fun ω => fieldEntropy energy spin observable (X ω)) μ := by
  have hL := lipschitzWith_fieldEntropy energy spin observable hspin hneg hpos hsignal
  have hdom := (hX.norm.const_mul ((Fintype.card V : ℝ) * 2)).add
    (integrable_const ‖fieldEntropy energy spin observable 0‖ : Integrable
      (fun _ : Ω => ‖fieldEntropy energy spin observable 0‖) μ)
  apply hdom.mono' (hL.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  filter_upwards [] with ω
  have hb := hL.norm_sub_le (X ω) 0
  simp only [sub_zero, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat] at hb
  calc
    ‖fieldEntropy energy spin observable (X ω)‖ ≤
        ‖fieldEntropy energy spin observable (X ω) - fieldEntropy energy spin observable 0‖ +
          ‖fieldEntropy energy spin observable 0‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add hb le_rfl

end Problem367.FinitePosterior

end

end OAI
