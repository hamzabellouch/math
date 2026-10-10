import OAI.Analysis.LipschitzHilbert.Trees.SourceMotionBudget

namespace OAI

/-! The actual relative mass-motion error is small even after multiplication
by the polynomial stopping threshold. These fixed-parameter bounds supply
the source's exceptional-cell argument. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_marking_parameters (D Kw A_M : ℝ)
    (hD : 0 ≤ D) (hKw : 0 < Kw) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let q := Real.exp δ*δ
      q ≤ 1/8 ∧ (1+q)*L^A_M < L^A_M+1 := by
  let C := 5*D/Kw
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_source_polynomial_motion (8*Real.exp C*C) A_M,
    eventually_ge_atTop (1:ℝ)] with L hpoly hL
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hs : 1 ≤ Real.sqrt (SourceParameters.step L) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    simpa using hG
  have hδ : C/Real.sqrt (SourceParameters.step L) ≤ C := div_le_self hC hs
  have hδ0 : 0 ≤ C/Real.sqrt (SourceParameters.step L) := div_nonneg hC (Real.sqrt_nonneg _)
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have he := Real.exp_le_exp.mpr hδ
  have hqM : (Real.exp (C/Real.sqrt (SourceParameters.step L))*
      (C/Real.sqrt (SourceParameters.step L)))*L^A_M ≤ 1/8 := by
    have hgain : SourceParameters.step L^(-(1/4:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
    have hbound := hpoly.trans hgain
    have hq := mul_le_mul_of_nonneg_right he hδ0
    have hm := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (by linarith : 0 ≤ L) A_M)
    have heq : (8*Real.exp C*C)*L^A_M/Real.sqrt (SourceParameters.step L) =
        8*((Real.exp C*(C/Real.sqrt (SourceParameters.step L)))*L^A_M) := by ring
    rw [heq] at hbound
    linarith
  have hq0 : 0 ≤ Real.exp (C/Real.sqrt (SourceParameters.step L))*
      (C/Real.sqrt (SourceParameters.step L)) := mul_nonneg (Real.exp_pos _).le hδ0
  have hq := (mul_le_mul_of_nonneg_left hM hq0).trans hqM
  dsimp only
  change Real.exp (C/Real.sqrt (SourceParameters.step L))*(C/Real.sqrt (SourceParameters.step L)) ≤ 1/8 ∧ _
  refine ⟨by simpa only [mul_one] using hq,?_⟩
  change (1+Real.exp (C/Real.sqrt (SourceParameters.step L))*
    (C/Real.sqrt (SourceParameters.step L)))*L^A_M < L^A_M+1
  nlinarith

/-- The conclusion is uniform over the source weight scale Kw≥1. -/
theorem eventually_source_marking_parameters_uniform (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ Kw : ℝ, 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let q := Real.exp δ*δ
      q ≤ 1/8 ∧ (1+q)*L^A_M < L^A_M+1 := by
  filter_upwards [eventually_source_marking_parameters D 1 A_M hD (by norm_num) hAM,
    eventually_ge_atTop (1:ℝ)] with L hbase hL
  intro Kw hKw
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hd0 : 0 ≤ (5*D/Kw)/Real.sqrt (SourceParameters.step L) := by positivity
  have hd : (5*D/Kw)/Real.sqrt (SourceParameters.step L) ≤
      (5*D/1)/Real.sqrt (SourceParameters.step L) := by
    apply div_le_div_of_nonneg_right _ hs.le
    simpa only [div_one] using div_le_self (show 0 ≤ 5*D by positivity) hKw
  have hq := mul_le_mul (Real.exp_le_exp.mpr hd) hd hd0 (Real.exp_pos _).le
  dsimp only at hbase ⊢
  refine ⟨hq.trans hbase.1,?_⟩
  have hq1 : 1+Real.exp ((5*D/Kw)/Real.sqrt (SourceParameters.step L))*
      ((5*D/Kw)/Real.sqrt (SourceParameters.step L)) ≤
      1+Real.exp ((5*D/1)/Real.sqrt (SourceParameters.step L))*
        ((5*D/1)/Real.sqrt (SourceParameters.step L)) := by linarith
  have hm := mul_le_mul_of_nonneg_right hq1
    (Real.rpow_nonneg (by linarith : 0 ≤ L) A_M)
  exact hm.trans_lt hbase.2

end LipschitzHilbert

end

end OAI
