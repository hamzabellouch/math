import Mathlib
import OAI.Combinatorics.UniformKServer.FlexEstimates
import OAI.Combinatorics.UniformKServer.StarParameters

namespace OAI

                                
section

/-! Actual lower requirements of a finite-count star.  This connects the
rank superadditivity to the output formulas, and proves the marked slack
from the logarithmic parameter gap (including zero side mass). -/
noncomputable section
namespace UniformKServer.StarLower
open Finset StarRanks RankData RankFunctions FlexEstimates
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def childBeta (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  ParentBeta.trueParam (input d i) k t ω

def parentBeta (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  ParentBeta.trueParam (parentInput d) k t ω

def lower (d : Data Ω ι k) (β : ℝ) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  totalRank β (fun j => (input d i j).posterior t ω)

def parentLower (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  totalRank (parentBeta d t ω) (fun j => (parentInput d j).posterior t ω)

theorem child_allowed (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    allowed (childBeta d t ω i) := by
  apply ParentBeta.true_allowed _ hk
  exact (StarParameters.child_le_parent d t ω i).trans (parent_size_bound d t ω)

theorem parent_allowed (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    allowed (parentBeta d t ω) :=
  ParentBeta.true_allowed _ hk _ _ (parent_size_bound d t ω)

theorem parameter_le (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    parentBeta d t ω ≤ childBeta d t ω i := by
  have hsize : ParentScale.trueX (input d i) t ω ≤ ParentScale.trueX (parentInput d) t ω :=
    max_le_max_right _ (StarParameters.child_le_parent d t ω i)
  have hpos := ParentScale.true_positive (input d i) t ω
  have hp := ParentScale.true_positive (parentInput d) t ω
  have hk0 : (0:ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hr := div_le_div_of_nonneg_left hk0.le hpos hsize
  have hl := Real.log_le_log (div_pos hk0 hp) hr
  have hc : 0 ≤ ParentBeta.cBeta/EpochAlpha.ell k :=
    div_nonneg (by norm_num [ParentBeta.cBeta]) (le_trans (by norm_num) (EpochAlpha.ell_one k))
  simpa [parentBeta,childBeta,ParentBeta.trueParam,ParentBeta.param,add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hl hc) 3

theorem decomposition (d : Data Ω ι k) (β : ℝ) (t : ℕ) (ω : Ω) (i : ι) :
    lower d β t ω i = coreCount (flags d t ω i)-β*coreInput d t ω i+
      trueFlex (input d i) β t ω := by
  apply core_decomposition
  intro j hj
  have h := core_small (input d i j) t ω hj
  norm_num [pstar] at h ⊢
  linarith

theorem inactive (d : Data Ω ι k) (β : ℝ) (t : ℕ) (ω : Ω) (i : ι)
    (hi : held d t ω i=0) :
    lower d β t ω i=0 ∧ trueFlex (input d i) β t ω=0 := by
  cases hb : CoarseData.activeState (input d i) t ω with
  | none =>
    have hz := CoarseData.inactive_zero (input d i) t ω β hb
    exact ⟨hz.2.1,hz.2.2⟩
  | some b =>
    have ha := CoarseData.active_accuracy (input d i) t ω hb
    change CoarseData.heldSize (input d i) t ω=0 at hi
    rw [CoarseBridge.held_some (input d i) t ω hb] at hi
    norm_num [CoarseData.cutoff] at ha
    exfalso
    nlinarith [ha.1,ha.2.2]

theorem lower_nonneg (d : Data Ω ι k) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ lower d β t ω i := by
  unfold lower totalRank
  exact sum_nonneg fun _ _ => rank_nonneg hβ

theorem core_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ coreInput d t ω i :=
  SyntheticCore.input_nonneg (fun j => ((input d i j).posterior_range t ω).1) _

theorem flex_mono (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    trueFlex (input d i) (childBeta d t ω i) t ω ≤
      trueFlex (input d i) (parentBeta d t ω) t ω := by
  have hg := (gap_bounds (input d i) (parent_allowed d hk t ω) t ω).1
  have hT := flex_nonneg (input d i) (parent_allowed d hk t ω) t ω
  have hgn : 0 ≤ flexGap (input d i) t ω := (div_nonneg hT (by norm_num)).trans hg
  rw [flex_affine (input d i) (parentBeta d t ω)]
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr (parameter_le d hk t ω i)) hgn)

theorem parent_dominates (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, lower d (parentBeta d t ω) t ω i) ≤ parentLower d t ω :=
  rank_sum d t ω (parent_allowed d hk t ω)

/-- No active-size or positive side-mass hypothesis is used in this identity. -/
theorem lower_difference (d : Data Ω ι k) (β γ : ℝ) (t : ℕ) (ω : Ω) (i : ι) :
    lower d β t ω i-lower d γ t ω i =
      (γ-β)*(coreInput d t ω i+flexGap (input d i) t ω) := by
  rw [decomposition,decomposition,flex_affine (input d i) β γ]
  ring

/-- The source's dominant-output-slack inequality.  Its constant is explicit
and absolute, and the assertion retains u=0 and T=0. -/
theorem dominant_slack (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (s : EpochGeometry.State ι) (hs : EpochGeometry.valid (held d t ω) s)
    (o : ι) (ho : EpochGeometry.dominant s=some o) (U : ℝ)
    (hU : EpochParameters.sideReference (held d t ω) o U) :
    (ParentBeta.cBeta/288)*(U/EpochGeometry.total s.base)/EpochAlpha.ell k*
        trueFlex (input d o) (parentBeta d t ω) t ω ≤
      lower d (parentBeta d t ω) t ω o-lower d (childBeta d t ω o) t ω o := by
  have hg := StarParameters.dominant_gap d hk t ω s hs o ho U hU
  change (ParentBeta.cBeta/3)/EpochAlpha.ell k*(U/EpochGeometry.total s.base) ≤
    childBeta d t ω o-parentBeta d t ω at hg
  have hbn := sub_nonneg.mpr (parameter_le d hk t ω o)
  have hT := flex_nonneg (input d o) (parent_allowed d hk t ω) t ω
  have hgap := (gap_bounds (input d o) (parent_allowed d hk t ω) t ω).1
  have h1 := mul_le_mul_of_nonneg_left hgap hbn
  have h2 := mul_le_mul_of_nonneg_right hg (div_nonneg hT (by norm_num : (0:ℝ) ≤ 96))
  have h3 := mul_nonneg hbn (core_nonneg d t ω o)
  rw [lower_difference]
  calc
    _ = ((ParentBeta.cBeta/3)/EpochAlpha.ell k*(U/EpochGeometry.total s.base))*
        (trueFlex (input d o) (parentBeta d t ω) t ω/96) := by ring
    _ ≤ (childBeta d t ω o-parentBeta d t ω)*
        (trueFlex (input d o) (parentBeta d t ω) t ω/96) := h2
    _ ≤ _ := by nlinarith only [h1,h3]

end UniformKServer.StarLower

end


end

end OAI
