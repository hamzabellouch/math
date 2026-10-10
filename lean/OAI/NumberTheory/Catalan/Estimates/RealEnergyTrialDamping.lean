import OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialRat
import OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal

namespace OAI

noncomputable section
open Polynomial Set
open scoped BigOperators

namespace InternalCatalan

def realEnergyTrialTau (u : ℕ → ℝ) (e x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * realEnergyTau e ^ (k + 1) *
    (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)

def realEnergyTrialRho (u : ℕ → ℝ) (e x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * realEnergyRho e x ^ (k + 1) * x ^ (k + 1) /
    ((k + 1 : ℕ) : ℝ)

def realEnergyTrialSigma (u : ℕ → ℝ) (e s : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * realEnergySigma e s ^ (k + 1) *
    (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval s / ((k + 1 : ℕ) : ℝ)

theorem energy_one_sub_pow_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    1 - r ^ m ≤ (m : ℝ) * (1 - r) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hp : r ^ m ≤ 1 := pow_le_one₀ hr.1 hr.2
      have hm := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hr.2)
      simp only [pow_succ, Nat.cast_succ]
      nlinarith only [ih, hm]

private theorem energy_trial_term_norm_le (a b : ℝ) {m : ℕ}
    (hm : 0 < m) (hb : |b| ≤ 1) : ‖a * b / (m : ℝ)‖ ≤ |a| := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hm0]
  calc
    _ ≤ |a| * 1 / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (abs_nonneg a)) hm0.le
    _ = |a| / (m : ℝ) := by rw [mul_one]
    _ ≤ |a| := div_le_self (abs_nonneg a) hm1

theorem energy_trial_damping_term_norm_le (a b : ℝ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (hb : |b| ≤ 1) :
    ‖a * r ^ m * b / (m : ℝ) - a * b / (m : ℝ)‖ ≤ (1 - r) * |a| := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hp0 : 0 ≤ 1 - r ^ m := sub_nonneg.mpr (pow_le_one₀ hr.1 hr.2)
  have hpdiv : (1 - r ^ m) / (m : ℝ) ≤ 1 - r := by
    apply (div_le_iff₀ hm0).mpr
    simpa only [mul_comm] using energy_one_sub_pow_le hr m
  have hfactor : a * r ^ m * b / (m : ℝ) - a * b / (m : ℝ) =
      -a * (1 - r ^ m) * b / (m : ℝ) := by ring
  rw [hfactor]
  simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg hp0, abs_of_pos hm0]
  calc
    _ ≤ |a| * (1 - r ^ m) * 1 / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg a) hp0)) hm0.le
    _ = |a| * ((1 - r ^ m) / (m : ℝ)) := by ring
    _ ≤ |a| * (1 - r) := mul_le_mul_of_nonneg_left hpdiv (abs_nonneg a)
    _ = (1 - r) * |a| := mul_comm _ _

theorem energy_damped_trial_summable (u v : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (hv : ∀ k, |v k| ≤ 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * r ^ (k + 1) * v (k + 1) /
      ((k + 1 : ℕ) : ℝ)) := by
  apply ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
  intro k
  have hb : |r ^ (k + 1) * v (k + 1)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1 _)]
    have hp : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr.1 hr.2
    exact (mul_le_mul hp (hv (k + 1))
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  simpa only [mul_assoc] using
    energy_trial_term_norm_le (u (k + 1)) (r ^ (k + 1) * v (k + 1))
      (Nat.succ_pos k) hb

theorem energy_damped_trial_sub_le (u v : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (hv : ∀ k, |v k| ≤ 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |(∑' k : ℕ, u (k + 1) * r ^ (k + 1) * v (k + 1) /
        ((k + 1 : ℕ) : ℝ)) -
      (∑' k : ℕ, u (k + 1) * v (k + 1) / ((k + 1 : ℕ) : ℝ))| ≤
      (1 - r) * (∑' k : ℕ, |u k|) := by
  have hud : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hu
  have hbase : Summable (fun k : ℕ => u (k + 1) * v (k + 1) /
      ((k + 1 : ℕ) : ℝ)) := by
    simpa only [one_pow, mul_one] using
      energy_damped_trial_summable u v hu hv (r := 1) ⟨by norm_num, le_rfl⟩
  have hdamped := energy_damped_trial_summable u v hu hv hr
  have hdiff := hdamped.hasSum.sub hbase.hasSum
  have hbound := hdiff.norm_le_of_bounded (hud.hasSum.mul_left (1 - r))
    (fun k => energy_trial_damping_term_norm_le (u (k + 1)) (v (k + 1))
      hr (Nat.succ_pos k) (hv (k + 1)))
  have htail : (∑' k : ℕ, |u (k + 1)|) ≤ ∑' k : ℕ, |u k| := by
    have hsplit := hu.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hsplit
    linarith [abs_nonneg (u 0)]
  simpa only [Real.norm_eq_abs] using hbound.trans
    (mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr hr.2))

theorem realEnergyTrialTau_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * realEnergyTau e ^ (k + 1) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) := by
  have hr := realEnergyTau_bounds he
  exact energy_damped_trial_summable u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval x)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) (abs_lt.mpr hx).le)
    ⟨hr.1.le, hr.2.le⟩

theorem realEnergyTrialRho_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * realEnergyRho e x ^ (k + 1) * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ)) := by
  have hr := realEnergyRho_mem he hx
  exact energy_damped_trial_summable u (fun k => x ^ k) hu
    (fun k => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) (abs_lt.mpr hx).le)
    ⟨hr.1.le, hr.2.le⟩

theorem realEnergyTrialSigma_summable (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Summable (fun k : ℕ => u (k + 1) * realEnergySigma e s ^ (k + 1) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval s / ((k + 1 : ℕ) : ℝ)) := by
  have hr := realEnergySigma_mem he hs
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2.le
  exact energy_damped_trial_summable u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval s)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) hsabs)
    ⟨hr.1.le, hr.2.le⟩

theorem realEnergyTrialTau_sub_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |realEnergyTrialTau u e x - barrierTrialT u x| ≤ e * (∑' k : ℕ, |u k|) := by
  have hr := realEnergyTau_bounds he
  have hh := energy_damped_trial_sub_le u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval x)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) (abs_lt.mpr hx).le)
    (r := realEnergyTau e) ⟨hr.1.le, hr.2.le⟩
  change |realEnergyTrialTau u e x - barrierTrialT u x| ≤
    (1 - realEnergyTau e) * (∑' k : ℕ, |u k|) at hh
  have heq : 1 - realEnergyTau e = e := by unfold realEnergyTau; ring
  simpa only [heq] using hh

theorem realEnergyTrialRho_sub_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e x : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |realEnergyTrialRho u e x - barrierTrialS u x| ≤
      (2 * e) * (∑' k : ℕ, |u k|) := by
  have hr := realEnergyRho_mem he hx
  have hh := energy_damped_trial_sub_le u (fun k => x ^ k) hu
    (fun k => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) (abs_lt.mpr hx).le)
    (r := realEnergyRho e x) ⟨hr.1.le, hr.2.le⟩
  change |realEnergyTrialRho u e x - barrierTrialS u x| ≤
    (1 - realEnergyRho e x) * (∑' k : ℕ, |u k|) at hh
  have herr : 1 - realEnergyRho e x ≤ 2 * e := by
    linarith [(realEnergyRho_bounds he hx).1]
  exact hh.trans (mul_le_mul_of_nonneg_right herr (tsum_nonneg (fun k => abs_nonneg (u k))))

theorem realEnergyTrialSigma_sub_le (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {e s : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    |realEnergyTrialSigma u e s - barrierTrialT u s| ≤ e * (∑' k : ℕ, |u k|) := by
  have hr := realEnergySigma_mem he hs
  have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2.le
  have hh := energy_damped_trial_sub_le u (fun k => (Chebyshev.T ℝ (k : ℤ)).eval s)
    hu (fun k => Chebyshev.abs_eval_T_real_le_one (k : ℤ) hsabs)
    (r := realEnergySigma e s) ⟨hr.1.le, hr.2.le⟩
  change |realEnergyTrialSigma u e s - barrierTrialT u s| ≤
    (1 - realEnergySigma e s) * (∑' k : ℕ, |u k|) at hh
  have herr : 1 - realEnergySigma e s ≤ e := by
    linarith [(realEnergySigma_bounds he hs).1]
  exact hh.trans (mul_le_mul_of_nonneg_right herr (tsum_nonneg (fun k => abs_nonneg (u k))))

end InternalCatalan

end

end OAI
