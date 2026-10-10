import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaBudget
import OAI.Combinatorics.UniformKServer.StarOutputMovement

namespace OAI

                                       
section

/-! Pointwise charges which enter the actual finite-law star ledger. In
particular marking-side changes and deficit changes are not assumed free. -/
noncomputable section
namespace UniformKServer.StarLocalCharges
open Finset StarRanks StarSchedules CoarseData RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def wholesaleMass (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  if StarCaps.wholesale d t ω then (∑ i, held d t ω i)+(∑ i, held d (t+1) ω i) else 0

def coreChanges (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := ∑ i, coreChange (input d i) t ω

def endpoints (d : Data Ω ι k) (ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i, FineVariation.endpointVariation (input d i) ξ t ω

theorem wholesale_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ wholesaleMass d t ω := by
  unfold wholesaleMass
  split_ifs
  · exact add_nonneg (sum_nonneg fun i _ => held_nonneg d t ω i) (sum_nonneg fun i _ => held_nonneg d (t+1) ω i)
  · rfl

theorem core_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ coreChanges d t ω :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem endpoints_nonneg (d : Data Ω ι k) (ξ : ℝ) (t : ℕ) (ω : Ω) : 0 ≤ endpoints d ξ t ω :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem wholesale_path (d : Data Ω ι k) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, wholesaleMass d t ω) ≤
      203*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))+
      (∑ t ∈ range H, if parentRefresh d StarConstants.delta t ω then
        EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) := by
  have h := SideReferenceSchedule.wholesale_budget (fun s i => held_nonneg d s ω i)
    (fun s => parentRefresh d StarConstants.delta s ω) H
  have hv := sum_le_sum (s:=range H) fun t _ => EpochAlphaBudget.variation_le
    (fun i => held_nonneg d t ω i) (fun i => held_nonneg d (t+1) ω i)
  change (∑ t ∈ range H, wholesaleMass d t ω) ≤ _ at h
  linarith

theorem alpha_changes (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    AlphaFiniteInput.changes (StarOutputData.alphaData d) t ω=coreChanges d t ω := by
  unfold AlphaFiniteInput.changes coreChanges coreChange SyntheticCore.changes
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change (if flags d t ω i j=flags d (t+1) ω i j then (0:ℝ) else 1)=_
  simp only [flags,eq_comm]
  rfl

theorem side_flag_formula (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) :
    StarTrackers.sideFlags d StarConstants.delta t ω i j=
      match EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
      | none => false
      | some o => if i=o then false else flags d t ω i j := by
  unfold StarTrackers.sideFlags EpochSide.active
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simp
  | some o =>
    by_cases hi : i=o
    · simp [hi]
    · by_cases ha : 0 < held d t ω i
      · simp [hi,EpochParameters.mem_active,ha]
      · have hz := le_antisymm (le_of_not_gt ha) (held_nonneg d t ω i)
        simp [hi,EpochParameters.mem_active,ha,zero_flags d t ω i hz]

theorem side_changes_same (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (hr : StarCaps.wholesale d t ω=false) :
    SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤ coreChanges d t ω := by
  have hd := SideReferenceSchedule.not_reset_dominant hr
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  unfold SideFiniteInput.changes coreChanges SyntheticCore.changes coreChange
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  change (if StarTrackers.sideFlags d StarConstants.delta t ω i j=
    StarTrackers.sideFlags d StarConstants.delta (t+1) ω i j then (0:ℝ) else 1) ≤ _
  rw [side_flag_formula,side_flag_formula,hd]
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => split_ifs <;> norm_num at *
  | some o =>
    by_cases hi : i=o
    · simp only [hi]
      split_ifs <;> norm_num at *
    · simp only [ite_eq_right hi]
      simp only [flags,eq_comm]
      exact le_rfl

theorem side_changes_size (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤
      40*((∑ i, held d t ω i)+(∑ i, held d (t+1) ω i)) := by
  have hl : SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤
      (∑ i, RankData.coreCount (flags d t ω i))+(∑ i, RankData.coreCount (flags d (t+1) ω i)) := by
    rw [←sum_add_distrib]
    unfold SideFiniteInput.changes SyntheticCore.changes RankData.coreCount
    apply sum_le_sum
    intro i _
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro j _
    change (if StarTrackers.sideFlags d StarConstants.delta t ω i j=
      StarTrackers.sideFlags d StarConstants.delta (t+1) ω i j then (0:ℝ) else 1) ≤ _
    rw [side_flag_formula,side_flag_formula]
    cases h₀ : flags d t ω i j <;> cases h₁ : flags d (t+1) ω i j <;>
      cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) <;>
      cases hn : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω) <;>
      split_ifs <;> norm_num at *
  have h₀ := sum_le_sum (s:=univ) fun i _ => CoarseBridge.core_count_bound (input d i) t ω
  have h₁ := sum_le_sum (s:=univ) fun i _ => CoarseBridge.core_count_bound (input d i) (t+1) ω
  change (∑ i, RankData.coreCount (flags d t ω i)) ≤ ∑ i, 40*held d t ω i at h₀
  change (∑ i, RankData.coreCount (flags d (t+1) ω i)) ≤ ∑ i, 40*held d (t+1) ω i at h₁
  rw [←mul_sum] at h₀ h₁
  linarith

theorem side_changes (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    SideFiniteInput.changes (StarOutputData.sideData d hk) t ω ≤
      coreChanges d t ω+40*wholesaleMass d t ω := by
  cases hr : StarCaps.wholesale d t ω
  · simpa only [wholesaleMass,hr,Bool.false_eq_true,ite_false,mul_zero,add_zero] using side_changes_same d hk t ω hr
  · have hs := side_changes_size d hk t ω
    unfold wholesaleMass
    rw [hr]
    simp only [ite_true]
    linarith [core_nonneg d t ω]

theorem coarse_flex_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    FlexEstimates.estimateFlex (input d i) 3 sizeTolerance t ω ≤ 120*held d t ω i := by
  have h := ActualFineCaps.cap_bound (input d i) (β:=3) (factor:=1)
    (by norm_num [RankFunctions.allowed]) (show 0 < sizeTolerance by norm_num [sizeTolerance])
    (show sizeTolerance ≤ 1/2 by norm_num [sizeTolerance]) (by norm_num) t ω
  have hn : 0 ≤ RankData.coreCount (flags d t ω i) := sum_nonneg fun j _ => by split_ifs <;> norm_num
  change RankData.coreCount (flags d t ω i)+1*FlexEstimates.estimateFlex (input d i) 3 sizeTolerance t ω ≤ _ at h
  change _ ≤ 120*held d t ω i at h
  linarith

theorem deficit_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    deficit d StarConstants.delta t ω ≤ 120*∑ i, held d t ω i := by
  unfold deficit
  split
  · exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => held_nonneg d t ω i)
  · rename_i i hi
    exact (coarse_flex_bound d t ω i).trans
      (mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => held_nonneg d t ω j) (mem_univ i)) (by norm_num))

theorem deficit_same (d : Data Ω ι k) (t : ℕ) (ω : Ω) (hr : StarCaps.wholesale d t ω=false) :
    StarOutputMovement.deficitMove d t ω ≤ endpoints d sizeTolerance t ω+coreChanges d t ω := by
  have hd := SideReferenceSchedule.not_reset_dominant hr
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  unfold StarOutputMovement.deficitMove deficit
  rw [hd]
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simpa only [sub_self,abs_zero] using add_nonneg (endpoints_nonneg d sizeTolerance t ω) (core_nonneg d t ω)
  | some i =>
    apply (FineVariation.flex_step (input d i) (show RankFunctions.allowed 3 by norm_num [RankFunctions.allowed]) _ _ _).trans
    change _ ≤ (∑ j, FineVariation.endpointVariation (input d j) sizeTolerance t ω)+(∑ j, coreChange (input d j) t ω)
    rw [←sum_add_distrib]
    exact single_le_sum (f:=fun j => FineVariation.endpointVariation (input d j) sizeTolerance t ω+coreChange (input d j) t ω) (fun j _ => add_nonneg
      (sum_nonneg fun r _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (sum_nonneg fun r _ => by split_ifs <;> norm_num)) (mem_univ i)

theorem deficit_step (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    StarOutputMovement.deficitMove d t ω ≤ endpoints d sizeTolerance t ω+coreChanges d t ω+120*wholesaleMass d t ω := by
  cases hr : StarCaps.wholesale d t ω
  · simpa only [wholesaleMass,hr,Bool.false_eq_true,ite_false,mul_zero,add_zero] using deficit_same d t ω hr
  · have h := abs_sub (deficit d StarConstants.delta (t+1) ω) (deficit d StarConstants.delta t ω)
    rw [abs_of_nonneg (deficit_nonneg d _ (t+1) ω),abs_of_nonneg (deficit_nonneg d _ t ω)] at h
    change StarOutputMovement.deficitMove d t ω ≤ _ at h
    unfold wholesaleMass
    rw [hr]
    simp only [ite_true]
    linarith [deficit_bound d t ω,deficit_bound d (t+1) ω,endpoints_nonneg d sizeTolerance t ω,core_nonneg d t ω]

end UniformKServer.StarLocalCharges

end


end

end OAI
