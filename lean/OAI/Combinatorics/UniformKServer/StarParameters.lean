import Mathlib
import OAI.Combinatorics.UniformKServer.StarRanks
import OAI.Combinatorics.UniformKServer.ParentBeta
import OAI.Combinatorics.UniformKServer.ParameterGaps

namespace OAI

                                     
section

/-! Logarithmic child/parent parameter gaps for the actual finite-count star.
The only epoch input is the invariant of the concrete held-size schedule. -/
noncomputable section
namespace UniformKServer.StarParameters
open Finset RankData RankTracking CoarseData StarRanks EpochGeometry
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def childSize (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  totalSize (fun j => (input d i j).posterior t ω)
def parentSize (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  totalSize (fun j => (parentInput d j).posterior t ω)

theorem size_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ childSize d t ω i := by
  unfold childSize totalSize
  exact sum_nonneg fun j _ => sizeRank_nonneg _

theorem positive_accuracy (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) :
    (9/10)*childSize d t ω i ≤ held d t ω i ∧
      held d t ω i ≤ (11/10)*childSize d t ω i ∧ cutoff ≤ childSize d t ω i := by
  cases hb : activeState (input d i) t ω with
  | none =>
    have := CoarseBridge.held_none (input d i) t ω hb
    change held d t ω i=0 at this
    linarith
  | some b =>
    have h := active_accuracy (input d i) t ω hb
    have he := CoarseBridge.held_some (input d i) t ω hb
    change held d t ω i=b at he
    change (9/10)*childSize d t ω i ≤ b ∧ b ≤ (11/10)*childSize d t ω i ∧
      cutoff ≤ childSize d t ω i at h
    rwa [he]

theorem size_with_side (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    childSize d t ω i+(10/11)*side i (held d t ω) ≤ parentSize d t ω := by
  have hi : childSize d t ω i+(10/11)*side i (held d t ω) =
      ∑ j, if j=i then childSize d t ω j else (10/11)*held d t ω j := by
    rw [side,mul_sum]
    have he : childSize d t ω i=∑ j, if j=i then childSize d t ω j else 0 := by simp
    rw [he,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hi]
  apply le_trans _ (size_sum d t ω)
  apply sum_le_sum
  intro j _
  split_ifs
  · rfl
  · have h := CoarseBridge.held_bound (input d j) t ω
    change held d t ω j ≤ (11/10)*childSize d t ω j at h
    change (10/11)*held d t ω j ≤ childSize d t ω j
    linarith

theorem child_le_parent (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    childSize d t ω i ≤ parentSize d t ω := by
  have h := size_with_side d t ω i
  have hs := EpochParameters.side_nonneg (held_nonneg d t ω) i
  linarith

theorem size_ratio (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) :
    1+(9/11)*(side i (held d t ω)/held d t ω i) ≤
      parentSize d t ω/childSize d t ω i := by
  have hc := positive_accuracy d t ω i ha
  exact ParameterGaps.ratio_from_sizes (lt_of_lt_of_le (by norm_num [cutoff]) hc.2.2)
    ha hc.1 (EpochParameters.side_nonneg (held_nonneg d t ω) i) (size_with_side d t ω i)

theorem beta_difference (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) :
    ParentBeta.trueParam (input d i) k t ω-ParentBeta.trueParam (parentInput d) k t ω =
      ParentBeta.cBeta/EpochAlpha.ell k*Real.log (parentSize d t ω/childSize d t ω i) := by
  have hc := (positive_accuracy d t ω i ha).2.2
  have hp := hc.trans (child_le_parent d t ω i)
  have hm0 : 0 < childSize d t ω i := lt_of_lt_of_le (by norm_num [cutoff]) hc
  have hM0 := hm0.trans_le (child_le_parent d t ω i)
  have hk0 : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  change ParameterGaps.beta ParentBeta.cBeta (EpochAlpha.ell k) k cutoff
      (childSize d t ω i)-ParameterGaps.beta ParentBeta.cBeta (EpochAlpha.ell k) k cutoff
      (parentSize d t ω) = _
  exact ParameterGaps.beta_gap hk0 hm0 hM0 hc hp

theorem regular_gap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (s : State ι) (hs : valid (held d t ω) s) (i : ι)
    (ha : 0 < held d t ω i) (hi : dominant s ≠ some i) :
    (ParentBeta.cBeta/50)/EpochAlpha.ell k*
      SideParameters.height (total s.base) (held d t ω i) ≤
      ParentBeta.trueParam (input d i) k t ω-ParentBeta.trueParam (parentInput d) k t ω := by
  have hsides : (99/100)*total s.base/held d t ω i-1 ≤
      side i (held d t ω)/held d t ω i := by
    apply (le_div_iff₀ ha).mpr
    rw [sub_mul,div_mul_cancel₀ _ ha.ne',one_mul]
    linarith [(total_comparison hs).1,total_with_side (held d t ω) i]
  have hr : 1+(9/11)*((99/100)*total s.base/held d t ω i-1) ≤
      parentSize d t ω/childSize d t ω i := by
    have hh := mul_le_mul_of_nonneg_left hsides (show (0:ℝ)≤9/11 by norm_num)
    linarith [size_ratio d t ω i ha]
  have hlog := ParameterGaps.regular_epoch ha (regular_size hs hi) hr
  rw [beta_difference d hk t ω i ha]
  have hcoeff : 0 ≤ ParentBeta.cBeta/EpochAlpha.ell k :=
    div_nonneg (by norm_num [ParentBeta.cBeta]) (le_trans (by norm_num) (EpochAlpha.ell_one k))
  have hm := mul_le_mul_of_nonneg_left hlog hcoeff
  unfold SideParameters.height
  calc
    _ = ParentBeta.cBeta/EpochAlpha.ell k*((1+Real.log (total s.base/held d t ω i))/50) := by ring
    _ ≤ _ := hm

theorem dominant_gap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (s : State ι) (hs : valid (held d t ω) s) (o : ι) (ho : dominant s=some o)
    (U : ℝ) (hU : EpochParameters.sideReference (held d t ω) o U) :
    (ParentBeta.cBeta/3)/EpochAlpha.ell k*(U/total s.base) ≤
      ParentBeta.trueParam (input d o) k t ω-ParentBeta.trueParam (parentInput d) k t ω := by
  have hA := (dominant_spec ho).1
  have ha : 0 < held d t ω o := by have := (dominant_size hs ho).1; linarith
  have haA : held d t ω o ≤ (101/100)*total s.base := by
    have hi : held d t ω o ≤ total (held d t ω) :=
      single_le_sum (fun j _ => held_nonneg d t ω j) (mem_univ o)
    exact hi.trans (total_comparison hs).2
  have hUb : U ≤ (1001/1000)*side o (held d t ω) := by
    have hu := (div_le_iff₀ (show (0:ℝ)<1001/1000 by norm_num)).mp hU.2.1
    linarith
  have hr := ParameterGaps.dominant_ratio hA ha
    (EpochParameters.side_nonneg (held_nonneg d t ω) o) haA hUb (size_ratio d t ω o ha)
  have hlog := ParameterGaps.dominant_log (div_nonneg hU.1 hA.le)
    (EpochParameters.marked_u_upper hs ho hU).le hr
  rw [beta_difference d hk t ω o ha]
  have hcoeff : 0 ≤ ParentBeta.cBeta/EpochAlpha.ell k :=
    div_nonneg (by norm_num [ParentBeta.cBeta]) (le_trans (by norm_num) (EpochAlpha.ell_one k))
  have hm := mul_le_mul_of_nonneg_left hlog hcoeff
  calc
    _ = ParentBeta.cBeta/EpochAlpha.ell k*((U/total s.base)/3) := by ring
    _ ≤ _ := hm

end UniformKServer.StarParameters

end


end

end OAI
