import Mathlib
import OAI.Combinatorics.UniformKServer.StarOutputData
import OAI.Combinatorics.UniformKServer.EpochSideBudget
import OAI.Combinatorics.UniformKServer.AlphaFiniteLedger
import OAI.Combinatorics.UniformKServer.SideFiniteLedger

namespace OAI

                                      
section

/-! Parameter jumps of the two actual causal minimizers. -/
noncomputable section
namespace UniformKServer.StarActualJumps
open Finset StarRanks StarSchedules StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def alphaScale (k : ℕ) : ℝ := StarConstants.multiplier*EpochAlpha.ell k
def sideSlope (k : ℕ) : ℝ := 2000*(EpochAlpha.ell k/StarConstants.cw+1)

theorem scale_nonneg (k : ℕ) : 0 ≤ alphaScale k :=
  mul_nonneg (by norm_num [StarConstants.multiplier]) (le_trans (by norm_num) (EpochAlpha.ell_one k))

theorem slope_nonneg (k : ℕ) : 0 ≤ sideSlope k := by
  have he := EpochAlpha.ell_one k
  unfold sideSlope
  exact mul_nonneg (by norm_num) (add_nonneg (div_nonneg (by linarith) StarConstants.cw_pos.le) (by norm_num))

theorem alpha_scale (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    AlphaEmpty.scale ((alphaData d).param t ω) ≤ alphaScale k := by
  apply EpochAlphaJump.scale_bound
  exact scale_nonneg k

theorem side_slope (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    AdaptiveSide.slope ((sideData d hk).param t ω)=sideSlope k := rfl

theorem alpha_star_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    AlphaFiniteInput.star (alphaData d) t ω i ≤ 40*held d (t+1) ω i := by
  have h : AlphaFiniteInput.star (alphaData d) t ω i ≤ AlphaFiniteInput.input (alphaData d) (t+1) ω i :=
    (SyntheticCore.core_le_new _ _ _ _ (fun i j => (AlphaFiniteInput.post_range (alphaData d) (t+1) ω i j).1) i).2
  exact h.trans (core_bound d (t+1) ω i)

theorem side_star_bound (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    SideFiniteInput.star (sideData d hk) t ω i ≤ 40*held d (t+1) ω i := by
  have h : SideFiniteInput.star (sideData d hk) t ω i ≤ SideFiniteInput.input (sideData d hk) (t+1) ω i :=
    (SyntheticCore.core_le_new _ _ _ _ (fun i j => (SideFiniteInput.post_range (sideData d hk) (t+1) ω i j).1) i).2
  exact h.trans ((StarTrackers.side_core_le d StarConstants.delta (t+1) ω i).trans (core_bound d (t+1) ω i))

theorem alpha_jump (d : Data Ω ι k) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, |AlphaFiniteLedger.jump (alphaData d) t ω|) ≤
      4100000*alphaScale k*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))+
      4400*alphaScale k*(∑ t ∈ range H, if parentRefresh d StarConstants.delta t ω then
        EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) := by
  apply EpochAlphaBudget.jump_budget (fun t i => held_nonneg d t ω i) _ (scale_nonneg k)
  · have hp := EpochAlpha.ell_one k
    apply (div_le_one (by linarith : 0 < EpochAlpha.ell k)).2
    exact le_trans (by norm_num [StarConstants.ct]) hp
  · exact fun t => (alphaData d).param_valid t ω
  · exact fun t i => (AlphaFiniteInput.valid_input (alphaData d) ω).2.1 t i
  · exact fun t i => alpha_star_bound d t ω i
  · exact fun t => AlphaFiniteInput.star_supported_old (alphaData d) t ω
  · exact fun t => AlphaFiniteInput.star_supported_new (alphaData d) t ω
  · exact fun t => (AlphaFiniteInput.step (alphaData d) t ω).2.1
  · exact fun t => (AlphaFiniteInput.step (alphaData d) t ω).2.2.2.1

theorem side_jump (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, |SideFiniteLedger.jump (sideData d hk) t ω|) ≤
      97920*sideSlope k*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))+
      480*sideSlope k*(∑ t ∈ range H, if parentRefresh d StarConstants.delta t ω then
        EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) := by
  apply EpochSideBudget.jump_budget (fun t i => held_nonneg d t ω i) _ (EpochAlpha.ell k) StarConstants.cw
    (fun t => upper d StarConstants.delta t ω)
  · intro t ht
    exact (StarCaps.not_wholesale_upper d t ω ht).symm
  · exact fun t => (sideData d hk).param_valid t ω
  · exact fun t => deficit_nonneg d StarConstants.delta (t+1) ω
  · exact fun t i => (SideFiniteInput.valid_input (sideData d hk) ω).2.2.1 t i
  · exact fun t i => side_star_bound d hk t ω i
  · exact fun t => (SideFiniteInput.step (sideData d hk) t ω).2.1
  · exact fun t => (SideFiniteInput.step (sideData d hk) t ω).2.2.2.2.1

end UniformKServer.StarActualJumps

end


end

end OAI
