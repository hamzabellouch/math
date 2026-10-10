import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalCoupledHistories
import OAI.NumberTheory.Jacobsthal.Partitions.CanonicalCostCoordinates
import OAI.NumberTheory.Jacobsthal.Probability.EvenThresholdEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.LiveKilledPrefixes

open _root_.Set Preorder
open FiniteHistoryTransport CemeteryHistoryMap CemeteryKernel

variable {X : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem live_coordinate_original (E : Set X) (N k : ℕ) (hk : k ≤ N)
    (h : Hist X N) (z : X)
    (hz : killHist E N h ⟨k,Finset.mem_Iic.mpr hk⟩ = Sum.inl z) :
    h ⟨k,Finset.mem_Iic.mpr hk⟩ = z ∧
      aliveThrough E k (frestrictLe₂ (π := fun _ => X) hk h) := by
  rw [killHist_coordinate E N k hk h] at hz
  split_ifs at hz with ha
  · exact ⟨Sum.inl_injective hz,ha⟩
  · simp [dead] at hz

theorem live_prefix_preserved (E : Set X) (N k : ℕ) (hk : k ≤ N)
    (h : Hist X N) (z : X)
    (hz : killHist E N h ⟨k,Finset.mem_Iic.mpr hk⟩ = Sum.inl z)
    (j : ℕ) (hj : j ≤ k) :
    killHist E N h ⟨j,Finset.mem_Iic.mpr (hj.trans hk)⟩ =
      Sum.inl (h ⟨j,Finset.mem_Iic.mpr (hj.trans hk)⟩) := by
  have ha := (live_coordinate_original E N k hk h z hz).2
  have hjA : aliveThrough E j (frestrictLe₂ (π := fun _ => X) (hj.trans hk) h) := by
    intro i hi
    exact ha ⟨i,Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.2).trans hj)⟩ hi
  rw [killHist_coordinate E N j (hj.trans hk) h,ite_eq_left hjA]

end NumberTheoryLean.LiveKilledPrefixes

end

section

namespace NumberTheoryLean.CompletedArrivalOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open CemeteryKernel CemeteryHistoryMap LiveKilledPrefixes CanonicalCoupledHistories
open PrimeHistories PrimeKilledChain ActualCoupledHistories ActualProcessCoupling

def liveMember {X : Type*} (E : Set X) : Space X → Prop
  | .inl y => y ∈ E
  | .inr _ => False

theorem liveMember_measurable {X : Type*} [MeasurableSpace X] {E : Set X} (hE : MeasurableSet E) :
    MeasurableSet {y | liveMember E y} := measurableSet_sum_iff.mpr ⟨hE,MeasurableSet.empty⟩

def completedOccurrence {X : Type*} (E : Set X) (N : ℕ) (h : Hist (Space X) N) : Prop :=
  ∃ j : Fin N,liveMember E (atIndex N h j.succ)

theorem completedOccurrence_measurable {X : Type*} [MeasurableSpace X] {E : Set X}
    (hE : MeasurableSet E) (N : ℕ) : MeasurableSet {h | completedOccurrence E N h} := by
  simp only [completedOccurrence,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  have hc : Measurable (fun h : Hist (Space X) N => atIndex N h j.succ) := measurable_pi_apply _
  exact hc (liveMember_measurable hE)

theorem kill_completed_subset {X : Type*} [MeasurableSpace X] (D E : Set X) (N : ℕ) :
    (killHist D N) ⁻¹' {h | completedOccurrence E N h} ⊆ arrivalOccurrence E N := by
  rintro h ⟨j,hj⟩
  cases hy : atIndex N (killHist D N h) j.succ with
  | inr u => rw [hy] at hj; exact False.elim hj
  | inl y =>
    rw [hy] at hj
    have horig := (live_coordinate_original D N (j.1+1) (by have := j.isLt; omega) h y hy).1
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    change atIndex N h j.succ ∈ E
    rw [show atIndex N h j.succ=y from horig]
    exact hj

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem source_completed_occurrence_le (mesh : ℝ) (N : ℕ) {E : Set CostState} (hE : MeasurableSet E) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N
      ((mapHist (fun q => q.1.2) N) ⁻¹' {h | completedOccurrence E N h}) ≤
      finitePathMeasure (FlaggedSourceStart.typedState start.side start.ratio hs) N (arrivalOccurrence E N) := by
  rw [sourceHistoryLaw_canonical_event hw hell hS0 hS hr hs hsS mesh N (completedOccurrence_measurable hE N)]
  exact measure_mono (kill_completed_subset _ E N)
end NumberTheoryLean.CompletedArrivalOccurrence

end

section

namespace NumberTheoryLean.CanonicalGapExposure
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteGapExposure ArrivalKernelGeometry RegeneratingInverseBands
open CanonicalCostCoordinates Erdos970Dependency.MarkedVisits
attribute [local instance] Classical.propDecidable

def coordinate (N : ℕ) (h : RawHistory N) (j : Fin (N+1)) : CostState :=
  h ⟨j.1,Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.isLt)⟩

noncomputable def pathExposure (v a L : ℝ) (N : ℕ) (h : RawHistory N) : ℝ :=
  ∑ j : Fin (N+1),if a ≤ gapValue v (coordinate N h j) ∧ stateRatio (coordinate N h j).1 ≤ L
    then 1/gapValue v (coordinate N h j) else 0

theorem pathExposure_measurable (v a L : ℝ) (N : ℕ) : Measurable (pathExposure v a L N) := by
  unfold pathExposure
  apply Finset.measurable_sum
  intro j _
  have hc : Measurable (fun h : RawHistory N => coordinate N h j) := measurable_pi_apply _
  have hg := (gapValue_measurable v).comp hc
  have hs := stateRatio_measurable.comp (measurable_fst.comp hc)
  exact Measurable.ite ((measurableSet_le measurable_const hg).inter (measurableSet_le hs measurable_const))
    (measurable_const.div hg) measurable_const

theorem pathExposure_nonneg (v a L : ℝ) (N : ℕ) (h : RawHistory N) : 0 ≤ pathExposure v a L N h := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact one_div_nonneg.mpr (Real.exp_pos _).le
  · exact le_rfl

theorem canonical_gap_steps (v : ℝ) (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,∀ j : Fin N,
      gapValue v (coordinate N h j.succ)=
        nextGap (gapValue v (coordinate N h j.castSucc)) (stateRatio (coordinate N h j.succ).1) := by
  have hall : ∀ᵐ h ∂finitePathMeasure s N,∀ j : Fin N,
      (coordinate N h j.succ).2=(coordinate N h j.castSucc).2+cost (stateRatio (coordinate N h j.succ).1) := by
    apply ae_all_iff.mpr
    intro j
    exact raw_cost_coordinate (Nat.zero_le _) j.isLt (fun _ => (s,0))
  filter_upwards [hall] with h hh
  intro j
  have he : coordinate N h j.succ=((coordinate N h j.succ).1,
      (coordinate N h j.castSucc).2+cost (stateRatio (coordinate N h j.succ).1)) := Prod.ext rfl (hh j)
  calc
    _ = gapValue v ((coordinate N h j.succ).1,
      (coordinate N h j.castSucc).2+cost (stateRatio (coordinate N h j.succ).1)) := congrArg _ he
    _ = _ := gapValue_update v (coordinate N h j.castSucc) (coordinate N h j.succ).1

theorem canonical_exposure_bound (v : ℝ) {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,pathExposure v a L N h ≤ (L+2)/a := by
  filter_upwards [canonical_gap_steps v s N] with h hh
  exact finite_all_exposure ha hL N (fun j => gapValue v (coordinate N h j))
    (fun j => stateRatio (coordinate N h j).1) (fun _ => Real.exp_pos _)
    (fun j => valid_pos (stateRatio_valid _)) hh

theorem canonical_exposure_integral (v : ℝ) {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (s : State) (N : ℕ) :
    Integrable (pathExposure v a L N) (finitePathMeasure s N) ∧
      (∫ h,pathExposure v a L N h ∂finitePathMeasure s N) ≤ (L+2)/a := by
  have hb := canonical_exposure_bound v ha hL s N
  have hi : Integrable (pathExposure v a L N) (finitePathMeasure s N) := by
    apply (integrable_const ((L+2)/a)).mono' (pathExposure_measurable v a L N).aestronglyMeasurable
    filter_upwards [hb] with h hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pathExposure_nonneg v a L N h)] using hh
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi (integrable_const ((L+2)/a)) hb
  simpa only [integral_const,probReal_univ,one_smul] using hh
end NumberTheoryLean.CanonicalGapExposure

end

section

namespace NumberTheoryLean.CanonicalEvenArrivalSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open ActualCouplingUpdates ActualSupportIntervals CanonicalGapExposure

def evenArrivalSupport (y : CostState) : Prop := stateSide y.1=.even → 2 ≤ stateRatio y.1

theorem evenArrivalSupport_measurable : MeasurableSet {y | evenArrivalSupport y} := by
  have he : {y : CostState | evenArrivalSupport y}=
      {y : CostState | stateSide y.1=.even}ᶜ ∪ {y | 2 ≤ stateRatio y.1} := by
    ext y
    simp only [evenArrivalSupport,Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff]
    tauto
  rw [he]
  exact (measurable_fst (side_set_measurable .even)).compl.union
    (measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst))

theorem costKernel_even_output (z : CostState) : ∀ᵐ y ∂costKernel z,evenArrivalSupport y := by
  filter_upwards [costKernel_follows z,costKernel_lower_support z] with y hy hmin
  intro he
  cases hi : stateSide z.1 with
  | even =>
    have hh := hy.2
    rw [hi,he] at hh
    exact False.elim (Side.noConfusion hh)
  | odd =>
    rw [hi] at hmin
    exact (le_max_left (2:ℝ) _).trans hmin

theorem path_arrival_support {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsMarkovKernel K] {P : X → Prop} (hP : MeasurableSet {x | P x})
    (hOut : ∀ x,∀ᵐ y ∂K x,P y) (N : ℕ) (h₀ : Hist X 0) :
    ∀ᵐ h ∂pathKernel K N h₀,∀ j : Fin N,P (atIndex N h j.succ) := by
  apply ae_all_iff.mpr
  intro j
  have hm : Measurable (fun h : Hist X N => atIndex N h j.succ) := measurable_pi_apply _
  apply (ae_map_iff hm.aemeasurable hP).mp
  rw [atIndex_law]
  have he : K^(j.1+1)=K ∘ₖ (K^j.1) := by
    simpa only [Nat.add_comm,pow_one] using Kernel.pow_add K 1 j.1
  change ∀ᵐ y ∂(K^(j.1+1)) (last 0 h₀),P y
  rw [he]
  exact Kernel.ae_comp_of_ae_ae hP (Filter.Eventually.of_forall hOut)

theorem canonical_even_arrivals (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,∀ j : Fin N,
      stateSide (coordinate N h j.succ).1=.even → 2 ≤ stateRatio (coordinate N h j.succ).1 :=
  path_arrival_support costKernel evenArrivalSupport_measurable costKernel_even_output N (fun _ => (s,0))
end NumberTheoryLean.CanonicalEvenArrivalSupport

end

section

namespace NumberTheoryLean.ThresholdExposureBridge
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open ErdosEvenThreshold TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

theorem odd_threshold_zero_high_parent (s : OddState) {R d : ℝ} (hs : 5 < s.1) (hd1 : d ≤ 1) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' nearThreshold R d)=0 := by
  rw [← thresholdStrip_eq_near]
  have he : oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thresholdStrip R d)=oddKernel s (thresholdStrip R d) := by
    rw [← oddToEven_map_ratio s,Measure.map_apply measurable_subtype_coe (thresholdStrip_measurable R d)]
  rw [he,oddKernel_apply]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (thresholdStrip_measurable R d)] with t ht
  have ht4 := (strip_parameters hd1 ht).2
  have hn : ¬max 2 (s.1-1) ≤ t := by linarith [le_max_right (2:ℝ) (s.1-1)]
  have hz : oddDensity s t=0 := by
    change (if max 2 (s.1-1) ≤ t then _ else 0)=0
    exact ite_eq_right hn
  simp only [hz,ENNReal.ofReal_zero,Pi.zero_apply]

theorem odd_threshold_zero_small_gap (s : OddState) {R d : ℝ} (hR : R ≤ 4) (hd1 : d ≤ 1) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' nearThreshold R d)=0 := by
  rw [← thresholdStrip_eq_near,thresholdStrip_empty hR hd1]
  simp

noncomputable def thresholdHazard (R d : ℝ) : State → ℝ
  | .inl _ => 0
  | .inr s => (oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' nearThreshold R d)).toReal

theorem thresholdHazard_exposure (s : State) {R d : ℝ}
    (hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    thresholdHazard R d s ≤ stripConstant*d*(if 4 ≤ R ∧ stateRatio s ≤ 5 then 1/R else 0) := by
  have hC : 0 < stripConstant := stripConstant_pos
  cases s with
  | inl s =>
    change 0 ≤ _
    split_ifs <;> positivity
  | inr s =>
    by_cases hR4 : 4 ≤ R
    · by_cases hs : s.1 ≤ 5
      · simp only [thresholdHazard]
        split_ifs with hguard
        · simpa only [mul_one_div] using conditional_even_near_threshold_real s hR hd0 hd1
        · exact (hguard ⟨hR4,hs⟩).elim
      · rw [thresholdHazard,odd_threshold_zero_high_parent s (lt_of_not_ge hs) hd1]
        simp only [ENNReal.toReal_zero,stateRatio,Sum.elim_inr,hs,and_false,ite_false,mul_zero,le_refl]
    · rw [thresholdHazard,odd_threshold_zero_small_gap s (le_of_not_ge hR4) hd1]
      simp only [ENNReal.toReal_zero,hR4,false_and,ite_false,mul_zero,le_refl]

theorem canonical_total_threshold_hazard (v : ℝ) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,
      (∑ j : Fin (N+1),thresholdHazard (gapValue v (coordinate N h j)) d (coordinate N h j).1) ≤
        (7/4:ℝ)*stripConstant*d := by
  filter_upwards [canonical_exposure_bound v (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)≤5) s N] with h hh
  have hsum : (∑ j : Fin (N+1),thresholdHazard (gapValue v (coordinate N h j)) d (coordinate N h j).1) ≤
      stripConstant*d*pathExposure v 4 5 N h := by
    rw [pathExposure,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact thresholdHazard_exposure _ (Real.exp_pos _) hd0 hd1
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg stripConstant_pos.le hd0)
  calc
    _ ≤ stripConstant*d*((5+2)/4) := hsum.trans hm
    _ = _ := by ring
end NumberTheoryLean.ThresholdExposureBridge

end

section

namespace NumberTheoryLean.CoupledEvenArrivalSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CanonicalGapExposure
open FiniteHistoryOccurrence
open CanonicalEvenArrivalSupport CanonicalCoupledHistories CemeteryHistoryMap LiveKilledPrefixes
open ActualCouplingUpdates ActualCoupledHistories ActualProcessCoupling
open PrimeHistories PrimeKilledChain LowStateHorizon

theorem killed_even_coordinate {E : Set CostState} (hE : MeasurableSet E)
    (s : State) (N : ℕ) (j : Fin N) :
    ∀ᵐ h ∂(finitePathMeasure s N).map (killHist E N),
      liftPredicate evenArrivalSupport (atIndex N h j.succ) := by
  have hP : MeasurableSet {h : Hist (CemeteryKernel.Space CostState) N |
      liftPredicate evenArrivalSupport (atIndex N h j.succ)} :=
    (measurable_pi_apply _) (liftPredicate_measurable evenArrivalSupport_measurable)
  apply (ae_map_iff (killHist_measurable hE N).aemeasurable hP).mpr
  filter_upwards [canonical_even_arrivals s N] with h hh
  cases hy : atIndex N (killHist E N h) j.succ with
  | inr u => trivial
  | inl y =>
    have horig := (live_coordinate_original E N (j.1+1) (by have := j.isLt; omega) h y hy).1
    change evenArrivalSupport y
    rw [← horig]
    exact hh j

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_even_arrivals (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ j : Fin N,∀ y : CostState,
        (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.2=Sum.inl y →
        stateSide y.1=.even → 2 ≤ stateRatio y.1 := by
  have hall : ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,∀ j : Fin N,
      liftPredicate evenArrivalSupport ((h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.2) := by
    apply ae_all_iff.mpr
    intro j
    have hP : MeasurableSet {h : Hist (CemeteryKernel.Space CostState) N |
        liftPredicate evenArrivalSupport (atIndex N h j.succ)} :=
      (measurable_pi_apply _) (liftPredicate_measurable evenArrivalSupport_measurable)
    have hh : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
        (mapHist (fun q => q.1.2) N),liftPredicate evenArrivalSupport (atIndex N h j.succ) := by
      rw [sourceHistoryLaw_canonical hw hell hS0 hS hr hs hsS mesh N]
      exact killed_even_coordinate (lowDomain_measurable _ _ _) _ N j
    exact (ae_map_iff (mapHist_measurable (by exact measurable_snd.comp measurable_fst) N).aemeasurable hP).mp hh
  filter_upwards [hall] with h hh
  intro j y hy he
  have hp := hh j
  rw [hy] at hp
  exact hp he
end NumberTheoryLean.CoupledEvenArrivalSupport

end

section

namespace NumberTheoryLean.ActualThresholdArrival
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures ArrivalKernelGeometry RegeneratingInverseBands
open ThresholdExposureBridge ErdosEvenThreshold RepresentativeStopGeometry KernelDensityBridge
open ActualCouplingUpdates

noncomputable def thresholdArrival (v d : ℝ) : Set CostState :=
  {y | stateSide y.1=.even ∧ 1 < currentExponent v y ∧
    0 ≤ gapValue v y-sourceHeight (currentExponent v y) ∧
    gapValue v y-sourceHeight (currentExponent v y) ≤ d}

theorem thresholdArrival_measurable (v d : ℝ) : MeasurableSet (thresholdArrival v d) := by
  have hH : Measurable (fun y => sourceHeight (currentExponent v y)) :=
    ((measurable_const.mul (currentExponent_measurable v))).max
      ((currentExponent_measurable v).add_const 2)
  have hslack := (gapValue_measurable v).sub hH
  exact (measurable_fst (side_set_measurable .even)).inter
    ((measurableSet_lt measurable_const (currentExponent_measurable v)).inter
      ((measurableSet_le measurable_const hslack).inter (measurableSet_le hslack measurable_const)))

theorem thresholdArrival_update (v d : ℝ) (z : CostState) (s : State) :
    (s,z.2+cost (stateRatio s)) ∈ thresholdArrival v d ↔
      stateSide s=.even ∧ stateRatio s ∈ nearThreshold (gapValue v z) d := by
  change stateSide s=.even ∧ _ ↔ _
  rw [currentExponent_update,gapValue_update]
  rfl

theorem thresholdHazard_eq_actual (v d : ℝ) (z : CostState) :
    thresholdHazard (gapValue v z) d z.1=(costKernel z (thresholdArrival v d)).toReal := by
  rw [costKernel_apply z (thresholdArrival_measurable v d)]
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    change 0=(evenBranch s {t | (t,T+cost (stateRatio t)) ∈ thresholdArrival v d}).toReal
    rw [evenBranch,Kernel.map_apply' _ measurable_inr _]
    · have he : Sum.inr ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thresholdArrival v d}=∅ := by
        ext t
        change (Sum.inr t,T+cost (stateRatio (Sum.inr t))) ∈ thresholdArrival v d ↔ False
        rw [thresholdArrival_update v d ((Sum.inl s),T)]
        simp [stateSide]
      rw [he,measure_empty,ENNReal.toReal_zero]
    · exact (measurable_id.prodMk
        (measurable_const.add (cost_measurable.comp stateRatio_measurable))) (thresholdArrival_measurable v d)
  | inr s =>
    change _=(oddBranch s {t | (t,T+cost (stateRatio t)) ∈ thresholdArrival v d}).toReal
    rw [oddBranch,Kernel.map_apply' _ measurable_inl _]
    · have he : Sum.inl ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thresholdArrival v d}=
          (Subtype.val : TransitionKernels.EvenState → ℝ) ⁻¹' nearThreshold (gapValue v ((Sum.inr s),T)) d := by
        ext t
        change (Sum.inl t,T+cost (stateRatio (Sum.inl t))) ∈ thresholdArrival v d ↔ _
        rw [thresholdArrival_update v d ((Sum.inr s),T)]
        simp only [stateSide,stateRatio,Sum.elim_inl,true_and,Set.mem_preimage]
      rw [he]
      rfl
    · exact (measurable_id.prodMk
        (measurable_const.add (cost_measurable.comp stateRatio_measurable))) (thresholdArrival_measurable v d)

theorem actualHazard_measurable (v d : ℝ) :
    Measurable (fun z : CostState => thresholdHazard (gapValue v z) d z.1) := by
  simp_rw [thresholdHazard_eq_actual]
  exact (costKernel.measurable_coe (thresholdArrival_measurable v d)).ennreal_toReal

theorem actualHazard_bounds (v d : ℝ) (z : CostState) :
    0 ≤ thresholdHazard (gapValue v z) d z.1 ∧ thresholdHazard (gapValue v z) d z.1 ≤ 1 := by
  rw [thresholdHazard_eq_actual]
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩
end NumberTheoryLean.ActualThresholdArrival

end

end Erdos970

end OAI
