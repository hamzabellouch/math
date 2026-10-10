import OAI.NumberTheory.Ostmann.ZeroDensity.ContourTail
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyContourScales

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.ZeroDensity

theorem eventually_supply_tail_decay (B : ℕ) (D E : ℝ)
    (hE : (B : ℝ)+D+1 ≤ E) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      (Q : ℝ)^2*(supplyPrimeSample L : ℝ)*
          ((Q : ℝ)*((supplyContourHeight (B+2) E L : ℝ)+2))^B /
          (supplyContourHeight (B+2) E L : ℝ)^(B+1)*
          (1+Real.log (supplyPrimeSample L : ℝ))^B ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  have hdecay := eventually_constant_exp_decay (C := (6 : ℝ)^B) (by positivity) D
  filter_upwards [hdecay,eventually_ge_atTop (1 : ℝ)] with L hdecay hL
  intro Q hQ hQQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hH : (2 : ℝ) ≤ supplyContourHeight (B+2) E L := by
    exact_mod_cast supplyContourHeight_ge_two (B+2) E L
  have hlo := log_supplyPrimeSample_lower L
  have hup := (log_supplyPrimeSample_bounds hL).2
  have hheight : (Q : ℝ)^(B+2)*Real.exp (E*L) ≤
      supplyContourHeight (B+2) E L := by
    have hpow := pow_le_pow_left₀ hQr.le
      (show (Q : ℝ) ≤ supplyConductorCutoff L by exact_mod_cast hQQ) (B+2)
    have hh := supplyContourHeight_lower (B+2) E L
    have hmul := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (E*L)).le
    have hnon : 0 ≤ (supplyConductorCutoff L : ℝ)^(B+2)*Real.exp (E*L) := by positivity
    nlinarith only [hh,hmul,hnon]
  have ht := contour_tail_power_bound B hQr hH (by linarith)
    (show 0 ≤ Real.log (supplyPrimeSample L : ℝ) by have := Real.exp_pos L; linarith)
    hup hheight
  have hexp : Real.exp (((B : ℝ)-E)*L) ≤ Real.exp (-(D+1)*L) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hE (show 0 ≤ L by linarith)
    nlinarith
  calc
    _ = (supplyPrimeSample L : ℝ)*((Q : ℝ)^2*
          ((Q : ℝ)*((supplyContourHeight (B+2) E L : ℝ)+2))^B /
          (supplyContourHeight (B+2) E L : ℝ)^(B+1)*
          (1+Real.log (supplyPrimeSample L : ℝ))^B) := by ring
    _ ≤ (supplyPrimeSample L : ℝ)*((6 : ℝ)^B*Real.exp (((B : ℝ)-E)*L)) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ ≤ (supplyPrimeSample L : ℝ)*((6 : ℝ)^B*Real.exp (-(D+1)*L)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg _)

end Ostmann.ZeroDensity

end

end OAI
