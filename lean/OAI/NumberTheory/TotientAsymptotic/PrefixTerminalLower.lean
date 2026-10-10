import OAI.NumberTheory.TotientAsymptotic.PrefixTerminalVolume
import OAI.NumberTheory.TotientAsymptotic.MassMajorant

namespace OAI

/-! A fixed terminal cutoff retains positive prefix volume. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefix_terminal_power_lower {B a : ℝ} (hB : 0 < B) (ha : 0 ≤ a)
    {N : ℕ} (hN : 0 < N) (hcost : 2*(N:ℝ)*a ≤ B) :
    B^N/2 ≤ (B-a)^N := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hab : a ≤ B := by nlinarith only [ha,hn,hcost]
  have hfrac : 0 ≤ 1-a/B := by
    have hh := (div_le_one hB).mpr hab
    linarith only [hh]
  have hb := one_add_mul_sub_le_pow (a:=1-a/B) (by linarith only [hfrac]) N
  have hc : (N:ℝ)*(a/B) ≤ 1/2 := by
    have hh : (2*(N:ℝ)*a)/B ≤ 1 := (div_le_iff₀ hB).mpr (by simpa using hcost)
    have he : (2*(N:ℝ)*a)/B=2*((N:ℝ)*(a/B)) := by ring
    rw [he] at hh
    linarith only [hh]
  have hp : (1/2:ℝ) ≤ (1-a/B)^N := by nlinarith only [hb,hc]
  have he : B-a=(1-a/B)*B := by field_simp
  rw [he,mul_pow]
  nlinarith only [mul_le_mul_of_nonneg_right hp (pow_nonneg hB.le N)]

theorem prefix_terminal_volume_lower {x : ℝ} (hB : 0 < B x)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hcost : 2*(N+1:ℝ)*g (N+1)*t ≤ B x) :
    G x (N+1)/2 ≤
      volume.real (prefixRegion (N+1) (B x) 0 0 ∩
        {u | t ≤ u (Fin.last N)}) := by
  have hg := g_pos (N+1)
  have hcost' : 2*((N+1:ℕ):ℝ)*(g (N+1)*t) ≤ B x := by
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using hcost
  have ha : 0 ≤ g (N+1)*t := mul_nonneg hg.le ht
  have hp := prefix_terminal_power_lower hB ha (by omega : 0 < N+1) hcost'
  have hab : g (N+1)*t ≤ B x := by
    nlinarith only [ha,hcost',show (1:ℝ) ≤ ((N+1:ℕ):ℝ) by exact_mod_cast (show 1 ≤ N+1 by omega)]
  have hd : 0 < (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)) :=
    mul_pos (by exact_mod_cast Nat.factorial_pos (N+1))
      (Finset.prod_pos (fun i _ => g_pos _))
  have hv := volume_prefixRegion_terminal N (B x) 0 (0 : Fin (N+1) → ℝ) ht
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero,
    max_eq_left (sub_nonneg.mpr hab)] at hv
  rw [Measure.real,hv,ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) hd.le)]
  unfold G
  rw [←prod_fin_shifted (N+1) g]
  have hh := div_le_div_of_nonneg_right hp hd.le
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
