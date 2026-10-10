import Mathlib
import OAI.Combinatorics.UniformKServer.StarFeasibilityParameters
import OAI.Combinatorics.UniformKServer.AllocationOutputs

namespace OAI

                                     
section

/-! Concrete data for the output rules, including the signed total cap error.
All rank and tracker quantities are derived from the finite hidden law. -/
noncomputable section
namespace UniformKServer.StarOutputData
open Finset StarRanks StarSchedules StarLower
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def core (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  RankData.coreCount (flags d t ω i)
def mass (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := ∑ i, coreInput d t ω i
def parentFlex (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  FlexEstimates.trueFlex (input d i) (parentBeta d t ω) t ω
def childFlex (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  FlexEstimates.trueFlex (input d i) (childBeta d t ω i) t ω

def error (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  match EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => 0
  | some o => StarCaps.flex d t ω o-parentFlex d t ω o

def alphaData (d : Data Ω ι k) : AlphaFiniteInput.Data Ω ι (Fin k) :=
  StarTrackers.alphaData d StarConstants.delta StarConstants.ct_pos
    StarConstants.ct_height StarConstants.multiplier_bound

def sideData (d : Data Ω ι k) (hk : 1 ≤ k) : SideFiniteInput.Data Ω ι (Fin k) :=
  StarTrackers.sideData d hk StarConstants.delta_bounds.1 StarConstants.cw_pos StarConstants.cw_height

def alpha (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ι → ℝ := AlphaFiniteInput.alpha (alphaData d) t ω

def side (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SideFiniteInput.tracker (sideData d hk) t ω

theorem mass_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ mass d t ω :=
  sum_nonneg fun i _ => core_nonneg d t ω i

theorem parent_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    0 ≤ parentLower d t ω := by
  unfold parentLower RankData.totalRank
  exact sum_nonneg fun _ _ => RankFunctions.rank_nonneg (parent_allowed d hk t ω)

theorem parent_expand (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) :
    (∑ i, (core d t ω i-parentBeta d t ω*coreInput d t ω i+parentFlex d t ω i)) ≤ q := by
  have h := (parent_dominates d hk t ω).trans hq
  simpa only [decomposition,core,parentFlex] using h

theorem child_expand (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    AllocationOutputs.lower (core d t ω) (coreInput d t ω) (childFlex d t ω)
      (childBeta d t ω) i=StarLower.lower d (childBeta d t ω i) t ω i :=
  (decomposition d (childBeta d t ω i) t ω i).symm

theorem flex_inactive (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) (hi : held d t ω i=0) :
    StarCaps.flex d t ω i=0 := by
  have h := StarCaps.inactive_cap d hk t ω i hi
  have hn : RankData.coreCount (flags d t ω i)=0 := by
    simp only [RankData.coreCount,zero_flags d t ω i hi,Bool.false_eq_true,ite_false,sum_const_zero]
  simpa only [StarCaps.cap,hn,zero_add] using h

theorem regular_flex (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω) ≠ some i) :
    childFlex d t ω i ≤ StarCaps.flex d t ω i ∧ StarCaps.flex d t ω i ≤ parentFlex d t ω i := by
  by_cases ha : 0 < held d t ω i
  · exact StarCaps.regular d hk t ω i ha hi
  · have hz := le_antisymm (le_of_not_gt ha) (held_nonneg d t ω i)
    rw [flex_inactive d hk t ω i hz]
    exact ⟨le_of_eq (StarLower.inactive d _ t ω i hz).2,
      le_of_eq ((StarLower.inactive d _ t ω i hz).2.symm)⟩

theorem cap_child (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    childFlex d t ω i ≤ StarCaps.flex d t ω i := by
  by_cases hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some i
  · exact (flex_mono d hk t ω i).trans (StarCaps.dominant d hk t ω i hi).1
  · exact (regular_flex d hk t ω i hi).1

theorem error_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : 0 ≤ error d t ω := by
  unfold error
  split
  · exact le_rfl
  · rename_i o ho
    exact sub_nonneg.mpr (StarCaps.dominant d hk t ω o ho).1

theorem error_sum (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, (StarCaps.flex d t ω i-parentFlex d t ω i)) ≤ error d t ω := by
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none =>
    simp only [error,ho]
    exact sum_nonpos fun i _ => sub_nonpos.mpr (regular_flex d hk t ω i (by rw [ho]; simp)).2
  | some o =>
    simp only [error,ho]
    rw [←sum_erase_add _ _ (mem_univ o)]
    have hs : (∑ i ∈ univ.erase o, (StarCaps.flex d t ω i-parentFlex d t ω i)) ≤ 0 := by
      apply sum_nonpos
      intro i hi
      apply sub_nonpos.mpr (regular_flex d hk t ω i ?_).2
      rw [ho]
      exact fun h => (ne_of_mem_erase hi) (Option.some.inj h).symm
    linarith

theorem error_rule_one (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (hreg : deficit d StarConstants.delta t ω/2 ≤ mass d t ω) :
    error d t ω ≤ (4*StarConstants.eps/EpochAlpha.ell k)*mass d t ω := by
  have hc : 0 ≤ StarConstants.eps/EpochAlpha.ell k := div_nonneg (by norm_num [StarConstants.eps])
    (le_trans (by norm_num) (EpochAlpha.ell_one k))
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none =>
    simp only [error,ho]
    exact mul_nonneg (by simpa only [mul_div_assoc] using mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) hc) (mass_nonneg d t ω)
  | some o =>
    have ht := (StarCaps.deficit_comparison d hk t ω o ho).1
    have he := (StarCaps.dominant d hk t ω o ho).2
    change StarCaps.flex d t ω o ≤ (1+StarConstants.eps/EpochAlpha.ell k)*parentFlex d t ω o at he
    change parentFlex d t ω o/2 ≤ _ at ht
    have hh := mul_le_mul_of_nonneg_left (show parentFlex d t ω o ≤ 4*mass d t ω by linarith) hc
    simp only [error,ho]
    simp only [div_eq_mul_inv] at he hh ⊢
    nlinarith only [he,hh]

theorem required_holes (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) :
    AllocationOutputs.excess (StarCaps.cap d t ω) q ≤ parentBeta d t ω*mass d t ω+error d t ω := by
  exact AllocationOutputs.required_holes (core d t ω) (coreInput d t ω) (parentFlex d t ω)
    (StarCaps.flex d t ω) (parentBeta d t ω) q (error d t ω)
    (core_nonneg d t ω) (by linarith [(parent_allowed d hk t ω).1])
    (error_nonneg d hk t ω) (parent_expand d hk t ω hq) (error_sum d hk t ω)

theorem alpha_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ alpha d t ω i :=
  (AlphaEmpty.state_interval (AlphaFiniteInput.alpha_state (alphaData d) t ω) i).1

theorem alpha_proportion (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    mass d (t+1) ω*alpha d (t+1) ω i ≤
      (1+AlphaEmpty.eta (StarFeasibilityParameters.alphaParam d (t+1) ω) i)*coreInput d (t+1) ω i :=
  (AlphaFiniteInput.step (alphaData d) t ω).2.2.1 i

theorem alpha_supported (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (hi : held d t ω i=0) :
    alpha d t ω i=0 := by
  have h := AlphaFiniteInput.alpha_state (alphaData d) t ω
  change AlphaEmpty.state (StarFeasibilityParameters.alphaParam d t ω) (alpha d t ω) at h
  have he := StarTrackers.alphaParam_active d StarConstants.delta StarConstants.ct StarConstants.multiplier t ω
  change AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω)=_ at he
  have hn : i ∉ AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω) := by
    rw [he,EpochParameters.mem_active,hi]
    exact lt_irrefl 0
  cases hp : StarFeasibilityParameters.alphaParam d t ω with
  | none => rw [hp] at h; rw [h]
  | some p => rw [hp] at h hn; exact h.2.1 i hn

theorem alpha_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (hi : 0 < held d t ω i) :
    (∑ j, alpha d t ω j)=1 := by
  have h := AlphaFiniteInput.alpha_state (alphaData d) t ω
  change AlphaEmpty.state (StarFeasibilityParameters.alphaParam d t ω) (alpha d t ω) at h
  have he := StarTrackers.alphaParam_active d StarConstants.delta StarConstants.ct StarConstants.multiplier t ω
  change AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω)=_ at he
  have hm : i ∈ AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω) := by
    rw [he,EpochParameters.mem_active]
    exact hi
  cases hp : StarFeasibilityParameters.alphaParam d t ω with
  | none => simp [hp,AlphaEmpty.active] at hm
  | some p => rw [hp] at h; exact h.2.2

theorem side_input_active (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : i ∈ (StarFeasibilityParameters.sideParam d t ω).active) :
    SideFiniteInput.input (sideData d hk) t ω i=coreInput d t ω i := by
  change SyntheticCore.input (fun j => (input d i j).posterior t ω)
    (StarTrackers.sideFlags d StarConstants.delta t ω i)=_
  change i ∈ EpochSide.active (held d t ω) (epoch d StarConstants.delta t ω) at hi
  apply congrArg (SyntheticCore.input (fun j => (input d i j).posterior t ω))
  funext j
  exact ite_eq_left hi

theorem core_inactive (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (hi : held d t ω i=0) :
    coreInput d t ω i=0 := by
  unfold coreInput
  exact SyntheticCore.no_flags _ (zero_flags d t ω i hi)

theorem side_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ side d hk t ω i := (SideFiniteInput.tracker_state (sideData d hk) t ω).1 i

theorem side_supported (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : i ∉ (StarFeasibilityParameters.sideParam d t ω).active) :
    side d hk t ω i=0 := (SideFiniteInput.tracker_state (sideData d hk) t ω).2.1 i hi

end UniformKServer.StarOutputData

end


end

end OAI
