import OAI.Analysis.LipschitzHilbert.Estimates.SharpRemainderDecay

namespace OAI

/-! The manuscript's time and averaging-width choices, with the exact
logarithmic long-time cost used by the sharp truncation argument. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def sharpSourceTime (L : ℝ) : ℝ := Real.exp (-(L^(97/100:ℝ)))
def sharpSourceWidthRatio (L : ℝ) : ℝ := Real.exp (L^(9/10:ℝ))

theorem sharpSourceTime_pos (L : ℝ) : 0<sharpSourceTime L := Real.exp_pos _
theorem sharpSourceWidthRatio_pos (L : ℝ) : 0<sharpSourceWidthRatio L := Real.exp_pos _

theorem eventually_sharpSourceParameters :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ sharpSourceTime L≤1/4 ∧ 10≤sharpSourceWidthRatio L := by
  have ht : Tendsto sharpSourceTime atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<97/100)))
  have hm : Tendsto sharpSourceWidthRatio atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10))
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    hm.eventually_ge_atTop 10] with L hL hT hmL
  exact ⟨hL,hT.le,hmL⟩

theorem sharpSourceTime_log (L R : ℝ) (hL : 1≤L) (hR : 0<R) (hR1 : R≤1) :
    Real.log (R/sharpSourceTime L)≤L := by
  rw [Real.log_div hR.ne' (sharpSourceTime_pos L).ne',sharpSourceTime,Real.log_exp,sub_neg_eq_add]
  have hr : Real.log R≤0 := Real.log_nonpos hR.le hR1
  have hp : L^(97/100:ℝ)≤L := Real.rpow_le_self_of_one_le hL (by norm_num)
  linarith

theorem sharpSourceWidthRatio_geometry (L w : ℝ) (hw : 0<w) (hm : 10≤sharpSourceWidthRatio L) :
    w≤sharpSourceWidthRatio L*w ∧ 5*(w/(sharpSourceWidthRatio L*w))≤1/2 := by
  have hm0 := sharpSourceWidthRatio_pos L
  constructor
  · nlinarith
  · have heq : w/(sharpSourceWidthRatio L*w)=1/sharpSourceWidthRatio L := by field_simp
    rw [heq]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
    have hi : (1:ℝ)/sharpSourceWidthRatio L≤1/10 := (one_div_le_one_div_of_le (by norm_num) hm)
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
