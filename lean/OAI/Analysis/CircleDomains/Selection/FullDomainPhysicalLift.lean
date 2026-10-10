import OAI.Analysis.CircleDomains.Probability.DomainPhysicalOccupation
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationPushforward

namespace OAI

/-! An arbitrary finite physical path wholly in the quotient domain has
an actual rectifiable physical lift with exactly the original occupation. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def fullDomainPhysicalLift (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) : RectifiablePath Y :=
  ⟨physicalSubpath d.domainEquiv (show (⊥ : PathTime) ≤ ⊤ from bot_le) ⟨γ.val, fun t _ => hγ t⟩,
    physicalSubpath_rectifiable d.domainEquiv hU (show (⊥ : PathTime) ≤ ⊤ from bot_le) γ.val (fun t _ => hγ t)
      d.basePoint γ.property⟩

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_mem (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) (t : PathTime) :
    (fullDomainPhysicalLift d hU γ hγ).val t ∈ d.physicalDomain :=
  physicalSubpath_mem d.domainEquiv (show (⊥ : PathTime) ≤ ⊤ from bot_le) _ t

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_value (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) (t : PathTime) :
    (fullDomainPhysicalLift d hU γ hγ).val t = (d.domainEquiv.symm ⟨γ.val t, hγ t⟩).val := by
  simp [fullDomainPhysicalLift, physicalSubpath, timeClip]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_project (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) :
    finiteProjectedPhysicalPath d.domainEquiv d.basePoint
      (fullDomainPhysicalLift d hU γ hγ) (fullDomainPhysicalLift_mem d hU γ hγ) = γ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (d.domainEquiv ⟨(fullDomainPhysicalLift d hU γ hγ).val t, _⟩).val = γ.val t
  simp only [fullDomainPhysicalLift_value]
  exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨γ.val t, hγ t⟩)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem fullDomainPhysicalLift_projects
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain)
    (π : Y → X) (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (t : PathTime) : π ((fullDomainPhysicalLift d hU γ hγ).val t) = γ.val t := by
  simpa [fullDomainPhysicalLift, timeClip] using
    physicalSubpath_projects d.domainEquiv π (fun y => (he y).symm)
      (show (⊥ : PathTime) ≤ ⊤ from bot_le) ⟨γ.val, fun t _ => hγ t⟩ t

omit [MeasurableSpace X] [BorelSpace X] in
theorem dyadicPhysicalOccupation_fullDomainLift
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) :
    dyadicPhysicalOccupation d.domainEquiv d.basePoint γ =
      pathOccupation (fullDomainPhysicalLift d hU γ hγ) := by
  calc
    _ = dyadicPhysicalOccupation d.domainEquiv d.basePoint
        (finiteProjectedPhysicalPath d.domainEquiv d.basePoint
          (fullDomainPhysicalLift d hU γ hγ) (fullDomainPhysicalLift_mem d hU γ hγ)) :=
      congrArg (dyadicPhysicalOccupation d.domainEquiv d.basePoint)
        (fullDomainPhysicalLift_project d hU γ hγ).symm
    _ = _ := dyadicPhysicalOccupation_project _ _ _ _

end CircleDomainRigidity

end

end OAI
