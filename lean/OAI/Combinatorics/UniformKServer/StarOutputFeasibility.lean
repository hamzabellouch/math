import Mathlib
import OAI.Combinatorics.UniformKServer.StarOutputData

namespace OAI

                                            
section

/-! Actual feasibility of both child-output formulas, at every positive time.
Regime inequalities are the literal hysteresis ranges. Degenerate active,
side, core and deficit values are not removed. -/
noncomputable section
namespace UniformKServer.StarOutputFeasibility
open Finset StarRanks StarSchedules StarLower StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def one (d : Data Ω ι k) (t : ℕ) (ω : Ω) (q : ℝ) : ι → ℝ :=
  AllocationOutputs.ruleOne (StarCaps.cap d t ω) (alpha d t ω) q

def two (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (o : ι) : ι → ℝ :=
  AllocationOutputs.ruleTwo (StarCaps.cap d t ω) (side d hk t ω) q
    (deficit d StarConstants.delta t ω) o

theorem one_inactive (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (i : ι)
    (hi : held d t ω i=0) : one d t ω q i=0 := by
  simp only [one,AllocationOutputs.ruleOne,StarCaps.inactive_cap d hk t ω i hi,
    alpha_supported d t ω i hi,mul_zero,sub_self]

theorem one_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d (t+1) ω ≤ q)
    (hreg : deficit d StarConstants.delta (t+1) ω/2 ≤ StarOutputData.mass d (t+1) ω) (i : ι) :
    lower d (childBeta d (t+1) ω i) (t+1) ω i ≤ one d (t+1) ω q i := by
  by_cases ha : 0 < held d (t+1) ω i
  · rw [←child_expand]
    by_cases ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some i
    · exact AllocationOutputs.rule_one_dominant (core d (t+1) ω) (coreInput d (t+1) ω)
        (childFlex d (t+1) ω) (StarCaps.flex d (t+1) ω) (childBeta d (t+1) ω)
        (AlphaEmpty.eta (StarFeasibilityParameters.alphaParam d (t+1) ω)) (alpha d (t+1) ω)
        (parentBeta d (t+1) ω) q (error d (t+1) ω)
        (core_nonneg d (t+1) ω) (alpha_nonneg d (t+1) ω) (alpha_sum d (t+1) ω i ha)
        (by linarith [(parent_allowed d hk (t+1) ω).1]) (error_nonneg d hk (t+1) ω)
        (required_holes d hk (t+1) ω hq) (alpha_proportion d t ω) i
        (StarFeasibilityParameters.dominant_room d hk (t+1) ω i ho)
        (by simp only [error,ho]
            have h := flex_mono d hk (t+1) ω i
            change childFlex d (t+1) ω i ≤ parentFlex d (t+1) ω i at h
            linarith)
    · exact AllocationOutputs.rule_one_regular (core d (t+1) ω) (coreInput d (t+1) ω)
        (childFlex d (t+1) ω) (StarCaps.flex d (t+1) ω) (childBeta d (t+1) ω)
        (AlphaEmpty.eta (StarFeasibilityParameters.alphaParam d (t+1) ω)) (alpha d (t+1) ω)
        (parentBeta d (t+1) ω) q (error d (t+1) ω) (4*StarConstants.eps/EpochAlpha.ell k)
        (core_nonneg d (t+1) ω) (alpha_nonneg d (t+1) ω)
        (by have hb := (parent_allowed d hk (t+1) ω).1
            have he : 0 ≤ 4*StarConstants.eps/EpochAlpha.ell k := div_nonneg
              (by norm_num [StarConstants.eps]) (by linarith [EpochAlpha.ell_one k])
            linarith)
        (required_holes d hk (t+1) ω hq) (error_rule_one d hk (t+1) ω hreg)
        (alpha_proportion d t ω) i (StarFeasibilityParameters.regular_room d hk (t+1) ω i ha ho)
        (cap_child d hk (t+1) ω i)
  · have hz := le_antisymm (le_of_not_gt ha) (held_nonneg d (t+1) ω i)
    rw [one_inactive d hk (t+1) ω q i hz,(StarLower.inactive d _ (t+1) ω i hz).1]

theorem one_upper (d : Data Ω ι k) (t : ℕ) (ω : Ω) (q : ℝ) (i : ι) :
    one d t ω q i ≤ StarCaps.cap d t ω i :=
  AllocationOutputs.rule_one_upper _ _ _ (alpha_nonneg d t ω) i

theorem one_budget (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) : (∑ i, one d t ω q i) ≤ q := by
  by_cases ha : ∃ i, 0 < held d t ω i
  · obtain ⟨i,hi⟩ := ha
    exact (AllocationOutputs.rule_one_budget (StarCaps.cap d t ω) (alpha d t ω) q
      (alpha_sum d t ω i hi)).le.trans (min_le_right _ _)
  · have hz : ∀ i, held d t ω i=0 := fun i => le_antisymm
      (le_of_not_gt (fun h => ha ⟨i,h⟩)) (held_nonneg d t ω i)
    simp only [one_inactive d hk t ω q _ (hz _),sum_const_zero]
    exact (parent_nonneg d hk t ω).trans hq

theorem side_upper (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    deficit d StarConstants.delta (t+1) ω*side d hk (t+1) ω i ≤
      childBeta d (t+1) ω i*coreInput d (t+1) ω i := by
  by_cases hi : i ∈ (StarFeasibilityParameters.sideParam d (t+1) ω).active
  · have h := (SideFiniteInput.step (sideData d hk) t ω).2.2.1 i
    rw [side_input_active d hk (t+1) ω i hi] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (StarFeasibilityParameters.side_room d hk (t+1) ω i hi) (core_nonneg d (t+1) ω i))
  · rw [side_supported d hk (t+1) ω i hi,mul_zero]
    exact mul_nonneg (by linarith [(child_allowed d hk (t+1) ω i).1]) (core_nonneg d (t+1) ω i)

theorem side_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some o)
    (hreg : StarOutputData.mass d (t+1) ω ≤ 2*deficit d StarConstants.delta (t+1) ω) (i : ι) (hi : i ≠ o) :
    (StarFeasibilityParameters.sideParam d (t+1) ω).b*coreInput d (t+1) ω i-
      deficit d StarConstants.delta (t+1) ω*AdaptiveSide.theta (StarFeasibilityParameters.sideParam d (t+1) ω) i*
        AdaptiveSide.offset (StarFeasibilityParameters.sideParam d (t+1) ω) i ≤
      deficit d StarConstants.delta (t+1) ω*side d hk (t+1) ω i := by
  by_cases ha : i ∈ (StarFeasibilityParameters.sideParam d (t+1) ω).active
  · have h := (SideFiniteInput.step (sideData d hk) t ω).2.2.2.1 hreg i
    rw [side_input_active d hk (t+1) ω i ha] at h
    change (StarFeasibilityParameters.sideParam d (t+1) ω).b*coreInput d (t+1) ω i-
      AdaptiveSide.theta (StarFeasibilityParameters.sideParam d (t+1) ω) i*
      AdaptiveSide.offset (StarFeasibilityParameters.sideParam d (t+1) ω) i*
      deficit d StarConstants.delta (t+1) ω ≤
      deficit d StarConstants.delta (t+1) ω*side d hk (t+1) ω i at h
    nlinarith only [h]
  · have hn : held d (t+1) ω i=0 := by
      have hh : ¬ 0 < held d (t+1) ω i := by
        intro hh
        apply ha
        change i ∈ EpochSide.active (held d (t+1) ω) (epoch d StarConstants.delta (t+1) ω)
        simp only [EpochSide.active,ho,mem_erase,EpochParameters.mem_active]
        exact ⟨hi,hh⟩
      exact le_antisymm (le_of_not_gt hh) (held_nonneg d (t+1) ω i)
    rw [core_inactive d (t+1) ω i hn,side_supported d hk (t+1) ω i ha]
    rw [AdaptiveSide.theta,DomainTransport.extend_supported _ _ i ha]
    simp

theorem two_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d (t+1) ω ≤ q) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some o)
    (hreg : StarOutputData.mass d (t+1) ω ≤ 2*deficit d StarConstants.delta (t+1) ω) (i : ι) :
    lower d (childBeta d (t+1) ω i) (t+1) ω i ≤ two d hk (t+1) ω q o i := by
  rw [←child_expand]
  apply AllocationOutputs.rule_two_lower (core d (t+1) ω) (coreInput d (t+1) ω)
    (parentFlex d (t+1) ω) (childFlex d (t+1) ω) (StarCaps.flex d (t+1) ω)
    (childBeta d (t+1) ω) (side d hk (t+1) ω)
    (AdaptiveSide.theta (StarFeasibilityParameters.sideParam d (t+1) ω))
    (AdaptiveSide.offset (StarFeasibilityParameters.sideParam d (t+1) ω)) q
    (deficit d StarConstants.delta (t+1) ω) (parentBeta d (t+1) ω)
    (StarFeasibilityParameters.sideParam d (t+1) ω).b o
    (core_nonneg d (t+1) ω) (parent_expand d hk (t+1) ω hq)
    (ParentBeta.parameter_accuracy (parentInput d) StarConstants.delta_bounds.1 hk (t+1) ω).1
    (cap_child d hk (t+1) ω)
  · intro j hj
    apply (regular_flex d hk (t+1) ω j ?_).2
    rw [ho]
    exact fun h => hj (Option.some.inj h).symm
  · exact fun j _ => side_upper d hk t ω j
  · exact fun j hj => side_lower d hk t ω o ho hreg j hj
  · rw [child_expand]
    change _ ≤ RankData.coreCount (flags d (t+1) ω o)-parentBeta d (t+1) ω*coreInput d (t+1) ω o+
      FlexEstimates.trueFlex (input d o) (parentBeta d (t+1) ω) (t+1) ω-
        lower d (childBeta d (t+1) ω o) (t+1) ω o
    rw [←decomposition]
    exact StarFeasibilityParameters.side_slack d hk (t+1) ω o ho
  · linarith [(child_allowed d hk (t+1) ω o).1]

theorem two_upper (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (o i : ι) :
    two d hk t ω q o i ≤ StarCaps.cap d t ω i :=
  AllocationOutputs.rule_two_upper _ _ _ _ _ _ (deficit_nonneg d StarConstants.delta t ω)
    (fun j _ => side_nonneg d hk t ω j)

theorem two_budget (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (o : ι) :
    (∑ i, two d hk t ω q o i) ≤ q := AllocationOutputs.rule_two_budget ..

end UniformKServer.StarOutputFeasibility

end


end

end OAI
