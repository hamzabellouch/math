import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortMean
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicPrefix

namespace OAI

/-! Sum the literal typical energy over dyadic origins. Keeping the
coefficient fixed is essential when it is later resolved into characters. -/
namespace TwoPointCorrelations

open Finset MeasureTheory

lemma halasz_short_dyadic_cells (B : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    (∑ k ∈ Ico n (2*n), ‖shortExponentialSum B H α k‖) =
      ∫ x in (n:ℝ)..(2*n), ‖shortExponentialSum B H α x‖ := by
  have he := halasz_short_integral_cells B n n H α
  rw [show n+n=2*n by omega] at he
  rw [show 2*(n:ℝ)=((2*n:ℕ):ℝ) by push_cast; ring,he]
  symm
  apply sum_bij (fun v : ℕ => fun _ => n+v)
  · intro v hv
    exact mem_Ico.mpr ⟨by omega,by have := mem_range.mp hv; omega⟩
  · intro v _ w _ h
    omega
  · intro k hk
    have := mem_Ico.mp hk
    exact ⟨k-n,mem_range.mpr (by omega),by omega⟩
  · intro _ _
    rfl

theorem halasz_short_global_energy (B : ℕ → ℂ) (hB : OneBounded B)
    (X H K : ℕ) (hH : 0 < H) (hK : 1 ≤ K) (α ε : ℝ)
    (hε : 0 ≤ ε) (hbudget : 1 ≤ ε*K)
    (henergy : ∀ n : ℕ, K ≤ n → 2*n ≤ X →
      (∫ x in (n:ℝ)..(2*n), ‖shortExponentialSum B H α x‖^2)/
        ((n:ℝ)*(H:ℝ)^2) ≤ ε^2) :
    shortExponentialIntegral B X H α ≤ 2*ε*X*H+2*(K:ℝ)*H := by
  rw [shortExponentialIntegral_eq_sum]
  apply mrt_dyadic_prefix_bound _ X K H ε hK (Nat.cast_nonneg H) hε hbudget
    (fun _ => norm_nonneg _) (fun n => minor_arc_short_sum_trivial B hB H n α)
  intro n hn hnx
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hhr : (0:ℝ) < H := by exact_mod_cast hH
  have hmean := Real.le_sqrt_of_sq_le
    ((halasz_short_mean_square B hn0 hH α).trans (henergy n hn hnx))
  rw [Real.sqrt_sq hε] at hmean
  rw [halasz_short_dyadic_cells]
  simpa only [mul_assoc] using (div_le_iff₀ (mul_pos hnr hhr)).mp hmean


lemma halasz_sharp_log_error_comparison {L l : ℝ} (hL : 1 ≤ L)
    (hlo : L/2 ≤ l) (hhi : l ≤ L) :
    Real.log l/l^(1/80:ℝ) ≤ 2*(Real.log L/L^(1/80:ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < l := by linarith
  have hlog := Real.log_le_log hl0 hhi
  have hpow := Real.rpow_le_rpow_of_nonpos (show 0 < L/2 by positivity) hlo
    (show (-1/80:ℝ) ≤ 0 by norm_num)
  have htwo : (2:ℝ)^(1/80:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ 2 by norm_num) (show (1/80:ℝ) ≤ 1 by norm_num)
  have he : (2:ℝ)^(-1/80:ℝ)=((2:ℝ)^(1/80:ℝ))⁻¹ := by
    rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  rw [Real.div_rpow hL0.le (by norm_num : (0:ℝ)≤2),he,div_inv_eq_mul] at hpow
  have hp : l^(-1/80:ℝ) ≤ 2*L^(-1/80:ℝ) := by
    exact hpow.trans (by nlinarith only
      [mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hL0.le (-1/80))])
  have hll : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlp : 0 ≤ l^(-1/80:ℝ) := Real.rpow_nonneg hl0.le _
  have hh := mul_le_mul hlog hp hlp hll
  have hinv (x : ℝ) (hx : 0 ≤ x) : x^(-1/80:ℝ)=(x^(1/80:ℝ))⁻¹ := by
    rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg hx]
  rw [hinv l hl0.le,hinv L hL0.le] at hh
  convert hh using 1 <;> ring

lemma halasz_sharp_root_error_comparison {L l : ℝ} (hL : 1 ≤ L)
    (hlo : L/2 ≤ l) (hhi : l ≤ L) :
    Real.sqrt (Real.log l/l^(1/80:ℝ)) ≤ 2*Real.sqrt (Real.log L/L^(1/80:ℝ)) := by
  have hδ : 0 ≤ Real.log L/L^(1/80:ℝ) := div_nonneg (Real.log_nonneg hL) (by positivity)
  apply (Real.sqrt_le_sqrt (halasz_sharp_log_error_comparison hL hlo hhi)).trans
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity,by nlinarith [Real.sq_sqrt hδ]⟩

end TwoPointCorrelations

end OAI
