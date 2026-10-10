import OAI.Probability.RadialTransition.CellStability

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def scaledBumpProfile (R r : ℝ) : ℝ := (R ^ 3)⁻¹ * bumpProfile (r / R)

def scaledBump (R : ℝ) (x : Position) : ℝ := (R ^ 3)⁻¹ * bump (R⁻¹ • x)

theorem scaledBump_radial {R : ℝ} (hR : 0 < R) (x : Position) :
    scaledBump R x = scaledBumpProfile R ‖x‖ := by
  simp [scaledBump, scaledBumpProfile, bump, norm_smul, Real.norm_eq_abs,
    abs_of_pos hR, div_eq_mul_inv, mul_comm]

theorem integral_scaledBump {R : ℝ} (hR : 0 < R) :
    ∫ x : Position, scaledBump R x = 1 := by
  unfold scaledBump
  rw [integral_const_mul, Measure.integral_comp_inv_smul, integral_bump]
  simp [Position, abs_of_pos (pow_pos hR 3), hR.ne']

theorem scaledBumpProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledBumpProfile R r :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hR.le 3)) (bumpProfile_nonneg _)

theorem scaledBumpProfile_bound {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    |scaledBumpProfile R r| ≤ bumpIntegral⁻¹ := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [abs_of_nonneg (scaledBumpProfile_nonneg hR0 r)]
  unfold scaledBumpProfile
  apply le_trans (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (bumpProfile_bound (r / R)))
    (inv_nonneg.mpr (pow_nonneg hR0.le 3)))
  exact mul_le_of_le_one_left (inv_nonneg.mpr bumpIntegral_pos.le)
    (inv_le_one_of_one_le₀ (one_le_pow₀ hR))

theorem scaledBumpProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledBumpProfile R r = 0 := by
  rw [scaledBumpProfile, bumpProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)),
    mul_zero]

theorem continuous_scaledBumpProfile (R : ℝ) : Continuous (scaledBumpProfile R) :=
  continuous_const.mul (continuous_bumpProfile.comp (continuous_id.div_const _))

def attractionProfile (a R : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' n, a n * scaledBumpProfile (R n) r

def familyPotential (t : ℝ) (a R : ℕ → ℝ) : Potential :=
  fun r => coreReal t r - t * attractionProfile a R r

theorem attractionProfile_nonneg {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    0 ≤ attractionProfile a R r := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (ha n) (scaledBumpProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR n)) r)

theorem summable_attractionProfile {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (r : ℝ) :
    Summable (fun n => a n * scaledBumpProfile (R n) r) := by
  apply (hs.mul_right bumpIntegral⁻¹).of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (scaledBumpProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR n)) r)
  · intro n
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (scaledBumpProfile_bound (hR n) r)) (ha n)

theorem attractionProfile_bound {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (r : ℝ) :
    |attractionProfile a R r| ≤ (∑' n, a n) * bumpIntegral⁻¹ := by
  rw [abs_of_nonneg (attractionProfile_nonneg ha hR r)]
  unfold attractionProfile
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (scaledBumpProfile_bound (hR n) r)) (ha n))
    (summable_attractionProfile ha hR hs r) (hs.mul_right _)

theorem continuous_attractionProfile {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) :
    Continuous (attractionProfile a R) := by
  apply continuous_tsum (fun n => continuous_const.mul (continuous_scaledBumpProfile (R n)))
    (hs.mul_right bumpIntegral⁻¹)
  intro n r
  change |a n * scaledBumpProfile (R n) r| ≤ a n * bumpIntegral⁻¹
  rw [abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (scaledBumpProfile_bound (hR n) r) (ha n)

theorem continuous_familyPotential {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (t : ℝ) :
    Continuous (familyPotential t a R) := by
  exact ((continuous_coreReal t).sub (continuous_const.mul
    (continuous_attractionProfile ha hR hs))).comp NNReal.continuous_coe

theorem bounded_familyPotential {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (t : ℝ) :
    IsBoundedPotential (familyPotential t a R) := by
  refine ⟨t ^ 2 + |t| * ((∑' n, a n) * bumpIntegral⁻¹), ?_, ?_⟩
  · exact add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _)
      (mul_nonneg (tsum_nonneg ha) (inv_nonneg.mpr bumpIntegral_pos.le)))
  · intro r
    apply le_trans (abs_sub _ _)
    rw [abs_of_nonneg (coreReal_nonneg t r), abs_mul]
    exact add_le_add (coreReal_le t r)
      (mul_le_mul_of_nonneg_left (attractionProfile_bound ha hR hs r) (abs_nonneg t))

theorem familyPotential_nonpos_outer {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) {t : ℝ} (ht : 1 ≤ t)
    {r : ℝ≥0} (hr : 2 ≤ (r : ℝ)) : familyPotential t a R r ≤ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv : 1 / t ≤ 1 := by simpa using inv_le_one_of_one_le₀ ht
  have hz := coreReal_zero_outer ht0 (show 1 + 1 / t ≤ (r : ℝ) by linarith)
  dsimp [familyPotential]
  rw [hz, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg ht0.le (attractionProfile_nonneg ha hR r))

theorem scaledBumpProfile_decay {R r κ : ℝ} (hR : 1 ≤ R) (hr : 1 ≤ r)
    (hκ : 0 ≤ κ) :
    scaledBumpProfile R r ≤
      bumpIntegral⁻¹ * R ^ κ * r ^ (-(3 + κ)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  by_cases hcomp : R ≤ r
  · rw [scaledBumpProfile_zero hR0 hcomp]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr bumpIntegral_pos.le)
      (Real.rpow_nonneg hR0.le _)) (Real.rpow_nonneg hr0.le _)
  · have hrr : r ≤ R := le_of_not_ge hcomp
    have hm := Real.rpow_le_rpow_of_nonpos hr0 hrr (show -(3 + κ) ≤ 0 by linarith)
    have hcancel : R ^ κ * R ^ (-(3 + κ)) = (R ^ 3)⁻¹ := by
      rw [← Real.rpow_add hR0]
      have he : κ + -(3 + κ) = -(3 : ℝ) := by ring
      rw [he, Real.rpow_neg hR0.le]
      norm_cast
    calc
      _ ≤ (R ^ 3)⁻¹ * bumpIntegral⁻¹ := by
        apply mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (bumpProfile_bound _))
          (inv_nonneg.mpr (pow_nonneg hR0.le _))
      _ = bumpIntegral⁻¹ * (R ^ κ * R ^ (-(3 + κ))) := by rw [hcancel]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hR0.le κ))
          (inv_nonneg.mpr bumpIntegral_pos.le)

theorem attractionProfile_decay {a R : ℕ → ℝ} {κ : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hκ : 0 ≤ κ) (hweighted : Summable (fun n => a n * R n ^ κ))
    {r : ℝ} (hr : 1 ≤ r) :
    attractionProfile a R r ≤
      bumpIntegral⁻¹ * (∑' n, a n * R n ^ κ) * r ^ (-(3 + κ)) := by
  have hh := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (scaledBumpProfile_decay (hR n) hr hκ) (ha n))
    (summable_attractionProfile ha hR hs r)
    (show Summable (fun n => a n * (bumpIntegral⁻¹ * R n ^ κ * r ^ (-(3 + κ)))) from by
      apply ((hweighted.mul_left bumpIntegral⁻¹).mul_right (r ^ (-(3 + κ)))).congr
      intro n
      ring)
  have heq : (∑' n, a n * (bumpIntegral⁻¹ * R n ^ κ * r ^ (-(3 + κ)))) =
      bumpIntegral⁻¹ * (∑' n, a n * R n ^ κ) * r ^ (-(3 + κ)) := by
    simp_rw [show ∀ n, a n * (bumpIntegral⁻¹ * R n ^ κ * r ^ (-(3 + κ))) =
      (bumpIntegral⁻¹ * (a n * R n ^ κ)) * r ^ (-(3 + κ)) by intro n; ring]
    rw [tsum_mul_right, tsum_mul_left]
  exact hh.trans_eq heq

end RadialTransition

end

end OAI
