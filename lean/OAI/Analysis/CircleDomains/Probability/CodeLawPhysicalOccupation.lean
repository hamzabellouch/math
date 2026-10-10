import OAI.Analysis.CircleDomains.Topology.SphereLevels
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCode
import OAI.Analysis.CircleDomains.Probability.CodePathLaws
import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures

namespace OAI

/-! Forgetting tags preserves the actual mean physical occupation. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem meanPhysicalOccupation_codePathLaw (d : PathCodeData Sphere Sphere)
    (hU : IsOpen d.quotientDomain) (P : ProbabilityMeasure (BasePathCode d)) :
    meanPhysicalOccupation d.domainEquiv d.basePoint (codePathLaw d P) =
      meanCodeOccupation d P := by
  apply Measure.ext
  intro S hS
  have hm : Measurable (fun γ => physicalOccupationCode d.domainEquiv d.basePoint γ S) :=
    (Measure.measurable_coe hS).comp (measurable_physicalOccupationCode d.domainEquiv hU d.basePoint)
  rw [meanPhysicalOccupation_apply _ hU _ _ hS, meanCodeOccupation_apply d hU P hS,
    codePathLaw, ProbabilityMeasure.toMeasure_map, lintegral_map hm (measurable_codePath d)]
  apply lintegral_congr
  intro Γ
  exact congrArg (fun ν : Measure Sphere => ν S)
    (physicalOccupationCode_eq d.domainEquiv d.basePoint (baseCodePhysicalPath d Γ))

theorem codePathLaw_collar_endpoints (d : PathCodeData Sphere Sphere)
    (hU : IsOpen d.quotientDomain) (P : ProbabilityMeasure (BasePathCode d))
    (V : Set Sphere) (hV : IsOpen V) (hanchor : Disjoint d.anchor V) (hb : d.target ∈ V) :
    ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = d.target ∧ physicalDomainLength d.domainEquiv d.basePoint γ < ∞ := by
  change ∀ᵐ γ ∂(P : Measure (BasePathCode d)).map (codePath d), _
  apply (ae_map_iff (measurable_codePath d).aemeasurable ?_).mpr
  · exact Eventually.of_forall fun Γ =>
      ⟨fun hv => disjoint_left.mp hanchor Γ.property.2.1.1 hv,
       by change Γ.val.1 ⊤ ∈ V; rw [Γ.property.2.1.2.1]; exact hb,
       Γ.property.2.1.2.1, Γ.property.1.1⟩
  · exact (((continuous_eval_const ⊥).measurable hV.measurableSet).compl).inter
      (((continuous_eval_const ⊤).measurable hV.measurableSet).inter
        ((measurableSet_eq_fun (continuous_eval_const ⊤).measurable measurable_const).inter
          (measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint)))

end CircleDomainRigidity

end

end OAI
