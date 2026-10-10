import OAI.Probability.FreeIsing.Brownian.FourthMoment
import OAI.Probability.FreeIsing.Estimates.DyadicIncrementControl

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.BrownianDyadicMoments

def time (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0) ^ n

lemma time_succ (n k : ℕ) : time n (k + 1) = time n k + (1 / 2 : ℝ≥0) ^ n := by
  simp only [time, Nat.cast_add, Nat.cast_one, add_div, div_pow, one_pow]

lemma nndist_time_succ (n k : ℕ) :
    nndist (time n (k + 1)) (time n k) = (1 / 2 : ℝ≥0) ^ n := by
  rw [time_succ, NNReal.nndist_eq, add_tsub_cancel_left,
    tsub_eq_zero_of_le le_self_add, max_eq_left (by positivity)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

theorem ae_eventually_increments_of_fourth
    (hB : IsPreBrownianReal B μ) {C : ℝ}
    (hfourth : ∀ s t : ℝ≥0,
      (∫ ω, |B t ω - B s ω| ^ 4 ∂μ) ≤ C * (nndist t s : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ, ∀ᶠ n in atTop, ∀ k < K * 2 ^ n,
      |B (time n (k + 1)) ω - B (time n k) ω| ≤ (9 / 10 : ℝ) ^ n := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.2
  intro K
  let X : ∀ n, Fin (K * 2 ^ n) → Ω → ℝ :=
    fun n k ω => B (time n (k.val + 1)) ω - B (time n k.val) ω
  have hInt (n : ℕ) (k : Fin (K * 2 ^ n)) : Integrable (fun ω => |X n k ω| ^ 4) μ := by
    have hg := (hB.hasLaw_sub (time n (k.val + 1)) (time n k.val)).hasGaussianLaw
    simpa only [Real.norm_eq_abs, Pi.sub_apply, X] using
      (hg.memLp (p := (4 : ENNReal)) (by norm_num)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hMoment (n : ℕ) (k : Fin (K * 2 ^ n)) :
      (∫ ω, |X n k ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n := by
    have h := hfourth (time n k.val) (time n (k.val + 1))
    rw [nndist_time_succ] at h
    convert h using 1
    norm_num only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  filter_upwards [DyadicIncrementControl.ae_eventually_dyadic_grid_nine_tenths K X hInt hMoment]
    with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  exact hn ⟨k, hk⟩

theorem ae_eventually_increments (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ, ∀ᶠ n in atTop, ∀ k < K * 2 ^ n,
      |B (time n (k + 1)) ω - B (time n k) ω| ≤ (9 / 10 : ℝ) ^ n := by
  apply ae_eventually_increments_of_fourth hB (C := standardGaussianFourthMoment)
  intro s t
  simpa only [Real.norm_eq_abs, coe_nndist, NNReal.dist_eq] using
    (preBrownian_increment_fourth_moment hB s t).le

end Problem367.BrownianDyadicMoments

end

end OAI
