import OAI.Analysis.CircleDomains.Selection.FullDomainPhysicalLift
import OAI.Analysis.CircleDomains.Topology.IndicatorPathPenalty
import OAI.Analysis.CircleDomains.Selection.FirstEntryRestriction

namespace OAI

/-! A genuine bounded indicator density pays for a first-exit passage
through a relatively compact domain region. The estimate uses physical
arclength and remains valid for paths with arbitrary dust contacts elsewhere. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem first_exit_indicator_cost_lower_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain)
    (A : Set Y) {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀a ∈ A, ∀b ∉ π ⁻¹' O, δ ≤ edist a b)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hstart : γ.val ⊥ ∈ O) (hend : γ.val ⊤ ∉ O)
    (hA : (d.domainEquiv.symm ⟨γ.val ⊥, hOU (subset_closure hstart)⟩).val ∈ A)
    (m : X → ℝ≥0∞) :
    1 ≤ physicalTollCost d ((π ⁻¹' O).indicator (fun _ => δ⁻¹)) m γ := by
  let t := firstExitTime γ.val O
  have ht : (⊥ : PathTime) < t := firstExit_pos γ.val hO hstart hend
  let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ ht
  have hρU (s : PathTime) : ρ.val s ∈ d.quotientDomain := by
    apply hOU
    apply firstExit_initial_segment γ.val hO hstart hend
    exact (affinePathTime_mem_Icc ht.le s).2
  let β := fullDomainPhysicalLift d hU ρ hρU
  have hproject (s : PathTime) : π (β.val s) = ρ.val s :=
    fullDomainPhysicalLift_projects d hU ρ hρU π he s
  have hβA : β.val ⊥ ∈ A := by
    simpa only [β, fullDomainPhysicalLift_value, ρ, affineFinitePhysicalPath,
      affineRestrictedPath, ContinuousMap.comp_apply, affinePathTime_zero] using hA
  have hβout : β.val ⊤ ∉ π ⁻¹' O := by
    change π (β.val ⊤) ∉ O
    rw [hproject]
    change γ.val (affinePathTime ⊥ t ⊤) ∉ O
    rw [affinePathTime_one]
    exact firstExit_notMem γ.val hO hend
  have hβin (s : PathTime) (hs : s < ⊤) : β.val s ∈ π ⁻¹' O := by
    change π (β.val s) ∈ O
    rw [hproject]
    apply mem_before_firstExit γ.val O
    have h := affinePathTime_strictMono ht hs
    rwa [affinePathTime_one] at h
  let h : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => δ⁻¹)
  have hh : Measurable h := measurable_const.indicator (hO.preimage hπ).measurableSet
  have hpay : 1 ≤ ∫⁻y, h y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ := by
    rw [dyadicPhysicalOccupation_fullDomainLift d hU ρ hρU]
    exact indicator_occupation_pays_endpoint_distance β _ (hO.preimage hπ).measurableSet
      hβin hδ hδfin (hsep _ hβA _ hβout)
  have hfull : 1 ≤ physicalTollCost d h m ρ := hpay.trans le_self_add
  exact hfull.trans (physicalTollCost_affine_le d hU γ ht h hh m)

end CircleDomainRigidity

end

end OAI
