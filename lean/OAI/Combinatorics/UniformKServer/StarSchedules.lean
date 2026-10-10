import Mathlib
import OAI.Combinatorics.UniformKServer.FlexEstimates
import OAI.Combinatorics.UniformKServer.StarRanks
import OAI.Combinatorics.UniformKServer.ParentBeta
import OAI.Combinatorics.UniformKServer.CausalSchedules

namespace OAI

                                    
section

/-! The source star's actual causal data: persistent held sizes, parent refresh,
epochs, upper parameter and coarse dominant flexible-mass tracker. -/
noncomputable section
namespace UniformKServer.StarSchedules
open Finset StarRanks RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem refining (d : Data Ω ι k) {s t : ℕ} (hst : s ≤ t) {ω v : Ω}
    (h : (d.filtration t).r ω v) : (d.filtration s).r ω v := by
  induction hst with
  | refl => exact h
  | step hst ih => exact ih (d.refines _ _ _ h)

theorem estimate_measurable (d : Data Ω ι k) (i : ι) (j : Fin k) (f : ℝ → ℝ) (ξ : ℝ)
    (t : ℕ) {ω v : Ω} (h : (d.filtration t).r ω v) :
    estimate (input d i j) f ξ t ω=estimate (input d i j) f ξ t v :=
  congrArg f (reference_measurable (input d i j) f ξ t ω v h)

theorem held_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : held d t ω=held d t v := by
  funext i
  unfold held heldSize activeState
  congr 1
  apply CausalSchedules.active_congr
  intro s hs
  apply sum_congr rfl
  intro j _
  exact estimate_measurable d i j _ _ s (refining d hs h)

theorem parent_estimate_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) :
    sizeEstimate (parentInput d) δ t ω=sizeEstimate (parentInput d) δ t v := by
  apply sum_congr rfl
  intro j _
  exact congrArg RankData.sizeRank (reference_measurable (parentInput d j) _ δ t ω v h)

theorem parent_reference_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) :
    ParentScale.reference (parentInput d) δ t ω=ParentScale.reference (parentInput d) δ t v := by
  apply CausalSchedules.held_congr
  intro s hs
  unfold ParentScale.estimateX
  rw [parent_estimate_measurable d δ s (refining d hs h)]

def parentRefresh (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : Bool :=
  decide (ParentScale.reference (parentInput d) δ (t+1) ω ≠ ParentScale.reference (parentInput d) δ t ω)

theorem refresh_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration (t+1)).r ω v) : parentRefresh d δ t ω=parentRefresh d δ t v := by
  unfold parentRefresh
  rw [parent_reference_measurable d δ (t+1) h,
    parent_reference_measurable d δ t (d.refines t ω v h)]

def epoch (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : EpochGeometry.State ι :=
  EpochGeometry.schedule (fun s => held d s ω) (fun s => parentRefresh d δ s ω) t

theorem epoch_valid (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) :
    EpochGeometry.valid (held d t ω) (epoch d δ t ω) :=
  EpochGeometry.schedule_valid (fun s i => held_nonneg d s ω i) _ t

theorem epoch_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : epoch d δ t ω=epoch d δ t v :=
  CausalSchedules.epoch_congr t (fun s hs => held_measurable d s (refining d hs h))
    (fun s hs => refresh_measurable d δ s (refining d (by omega) h))

def upper (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ParentBeta.heldParam (parentInput d) δ k t ω

theorem upper_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : upper d δ t ω=upper d δ t v := by
  unfold upper ParentBeta.heldParam ParentScale.lowerX
  rw [parent_reference_measurable d δ t h]

theorem upper_allowed (d : Data Ω ι k) {δ : ℝ} (hδ : 0 < δ) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    RankFunctions.allowed (upper d δ t ω) :=
  ParentBeta.held_allowed (parentInput d) hδ hk t ω (parent_size_bound d t ω)

theorem flag_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : flags d t ω=flags d t v := by
  funext i j
  unfold flags RankData.core
  rw [absoluteReference_measurable (input d i j) (RankFunctions.pstar/8) t ω v h]

theorem flex_measurable (d : Data Ω ι k) (i : ι) (β ξ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) :
    FlexEstimates.estimateFlex (input d i) β ξ t ω=FlexEstimates.estimateFlex (input d i) β ξ t v := by
  apply sum_congr rfl
  intro j _
  have hf := congrFun (congrFun (flag_measurable d t h) i) j
  change RankData.core (input d i j) t ω=RankData.core (input d i j) t v at hf
  simp only [hf,FlexEstimates.term,estimate_measurable d i j _ _ t h]

def deficit (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  match EpochGeometry.dominant (epoch d δ t ω) with
  | none => 0
  | some o => FlexEstimates.estimateFlex (input d o) 3 sizeTolerance t ω

theorem deficit_nonneg (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ deficit d δ t ω := by
  unfold deficit
  split
  · rfl
  · apply sum_nonneg
    intro j _
    split_ifs
    · rfl
    · exact (FlexEstimates.term_range _ (by norm_num [RankFunctions.allowed]) _ _ _).1

theorem deficit_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : deficit d δ t ω=deficit d δ t v := by
  unfold deficit
  rw [epoch_measurable d δ t h]
  split
  · rfl
  · exact flex_measurable d _ _ _ t h

theorem core_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : coreInput d t ω=coreInput d t v := by
  funext i
  unfold coreInput
  rw [flag_measurable d t h]
  congr 1
  funext j
  exact (input d i j).posterior_measurable t ω v h

end UniformKServer.StarSchedules

end


end

end OAI
