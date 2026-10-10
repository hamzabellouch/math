import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryLogBins

namespace OAI

/-! # Uniform size bounds throughout the auxiliary power band -/
namespace JointDickman
open Filter
open scoped Topology

theorem auxiliary_range_scales (A : ℝ) {α β : ℝ} (hα : 0 < α) (hβ : β < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ,
      Real.exp (-1)*(N:ℝ)^α ≤ a → a ≤ (N:ℝ)^β →
      A ≤ a ∧ 1 ≤ a ∧ 2 ≤ (N:ℝ)/a ∧ 2*(N:ℝ) ≤ a^(4/α) := by
  have hgrow := ((tendsto_rpow_atTop hα).const_mul_atTop (Real.exp_pos (-1))).comp
    tendsto_natCast_atTop_atTop
  have hratio := (tendsto_rpow_atTop (show 0<1-β by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hlog := (eventually_auxiliary_log_lower hα).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hgrow.eventually (eventually_ge_atTop (max A 1)),
    hratio.eventually (eventually_ge_atTop 2),hlog,eventually_ge_atTop (2:ℕ)] with
    N hA hr hlog hN a ha haβ
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hN
  have ha1 : 1 ≤ a := (le_max_right A 1).trans (hA.trans ha)
  have ha0 : 0 < a := by linarith
  have htwo : 2*(N:ℝ)^β ≤ N := by
    calc
      _ ≤ (N:ℝ)^(1-β)*(N:ℝ)^β := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by rw [← Real.rpow_add hn]; norm_num
  have hlogA := (hlog a ha).2
  have hpow : (N:ℝ)^2 ≤ a^(4/α) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hn,Real.rpow_def_of_pos ha0]
    apply Real.exp_le_exp.mpr
    calc
      _ = (4/α)*((α/2)*Real.log (N:ℝ)) := by field_simp; ring
      _ ≤ (4/α)*Real.log a := mul_le_mul_of_nonneg_left hlogA (by positivity)
      _ = _ := mul_comm _ _
  refine ⟨(le_max_left A 1).trans (hA.trans ha),ha1,?_,?_⟩
  · apply (le_div_iff₀ ha0).mpr
    linarith
  · apply le_trans _ hpow
    have hn2 : (2:ℝ)≤N := by exact_mod_cast hN
    nlinarith

end JointDickman

end OAI
