import OAI.NumberTheory.Ostmann.ZeroDensity.RemainderDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyContourScales

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.ZeroDensity

theorem conductor_height_polynomial_le_exp (B : ℕ) {Q H : ℝ}
    (hQ : 1 ≤ Q) (hH : 2 ≤ H) :
    Q^2*(Q*(H+2))^B ≤
      Real.exp (((B : ℝ)+2)*(Real.log Q+Real.log (H+6))) := by
  have hQp : 0 < Q := by linarith
  have hHp : 0 < H+6 := by linarith
  have hqbase : Q ≤ Q*(H+6) := by nlinarith
  calc
    _ ≤ (Q*(H+6))^2*(Q*(H+6))^B := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ hQp.le hqbase 2
      · exact pow_le_pow_left₀ (by positivity) (by nlinarith : Q*(H+2) ≤ Q*(H+6)) B
      · positivity
      · positivity
    _ = (Q*(H+6))^(B+2) := by rw [pow_add]; ring
    _ = _ := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (mul_pos hQp hHp),
        Real.log_mul hQp.ne' hHp.ne']
      push_cast
      congr 1
      ring

theorem eventually_supply_left_edge_decay (B P : ℕ) {E : ℝ} (hE : 0 ≤ E) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      (Q : ℝ)^2*Real.sqrt (supplyPrimeSample L : ℝ)*
        ((Q : ℝ)*((supplyContourHeight P E L : ℝ)+2))^B ≤
          (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  let K : ℝ := ((B : ℝ)+2)*(20003*((P : ℝ)+1)+E+8)
  have hdecay := eventually_sqrt_subpower_decay K D
  filter_upwards [hdecay,eventually_ge_atTop (1 : ℝ)] with L hdecay hL
  intro Q hQ hQQ
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hH : (2 : ℝ) ≤ supplyContourHeight P E L := by
    exact_mod_cast supplyContourHeight_ge_two P E L
  have hp := conductor_height_polynomial_le_exp B hQr hH
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (supplyConductorCutoff L : ℝ) :=
    Real.log_le_log (by exact_mod_cast hQ) (by exact_mod_cast hQQ)
  have hb := supplyContourHeight_modulus_budget P hE hL
  unfold Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight at hb
  rw [abs_of_nonneg (Nat.cast_nonneg _)] at hb
  have hexp : ((B : ℝ)+2)*(Real.log (Q : ℝ)+Real.log ((supplyContourHeight P E L : ℝ)+6)) ≤
      K*L*Real.exp (9*L/10) := by
    have hh := mul_le_mul_of_nonneg_left (show Real.log (Q : ℝ)+
        Real.log ((supplyContourHeight P E L : ℝ)+6) ≤
        (20003*((P : ℝ)+1)+E+8)*L*Real.exp (9*L/10) by linarith)
      (show 0 ≤ (B : ℝ)+2 by positivity)
    dsimp [K]
    nlinarith only [hh]
  have hX : (1 : ℝ) < supplyPrimeSample L := by
    by_contra! hh
    have hl := Real.log_nonpos (Nat.cast_nonneg (supplyPrimeSample L)) hh
    have hlo := log_supplyPrimeSample_lower L
    have he := Real.exp_pos L
    linarith
  calc
    _ = Real.sqrt (supplyPrimeSample L : ℝ)*
        ((Q : ℝ)^2*((Q : ℝ)*((supplyContourHeight P E L : ℝ)+2))^B) := by ring
    _ ≤ Real.sqrt (supplyPrimeSample L : ℝ)*Real.exp (K*L*Real.exp (9*L/10)) :=
      mul_le_mul_of_nonneg_left (hp.trans (Real.exp_le_exp.mpr hexp)) (Real.sqrt_nonneg _)
    _ ≤ _ := hdecay _ hX (log_supplyPrimeSample_lower L)

end Ostmann.ZeroDensity

end

end OAI
