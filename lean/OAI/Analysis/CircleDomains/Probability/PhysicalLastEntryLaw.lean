import OAI.Analysis.CircleDomains.Probability.LastEntryLaw
import OAI.Analysis.CircleDomains.Selection.FinitePointAvoidance

namespace OAI

/-! Last-entry distributions on physical collar boundaries have no atoms. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem physical_lastEntryLaw_nullSingletonClass
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂sphericalArea) < ∞)
    (V : Set Sphere) (hV : IsOpen V) (hfront : frontier V ⊆ d.quotientDomain)
    (hinf : π OnePoint.infty ∉ frontier V)
    (hstart : Disjoint d.anchor V) (htarget : d.target ∈ V) :
    NullSingletonClass (lastEntryLaw (codePathLaw d P) V : Measure Sphere) := by
  apply lastEntryLaw_nullSingletonClass (codePathLaw d P) V hV
  · change ∀ᵐ γ ∂((P : Measure (BasePathCode d)).map (codePath d)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V
    apply (ae_map_iff (measurable_codePath d).aemeasurable
      (((continuous_eval_const ⊥).measurable hV.measurableSet).compl.inter
        ((continuous_eval_const ⊤).measurable hV.measurableSet))).mpr
    exact Eventually.of_forall fun Γ =>
      ⟨fun hv => disjoint_left.mp hstart Γ.property.2.1.1 hv,
       by change Γ.val.1 ⊤ ∈ V; rw [Γ.property.2.1.2.1]; exact htarget⟩
  · intro x hx
    let p : d.physicalDomain := d.domainEquiv.symm ⟨x, hfront hx⟩
    have hp : π p.val = x := by
      rw [← he p]
      exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hfront hx⟩)
    have hpfin : p.val ≠ OnePoint.infty := by
      intro h
      apply hinf
      simpa only [← hp, h] using hx
    cases heq : p.val using OnePoint.rec with
    | infty => exact (hpfin heq).elim
    | coe z =>
      have hz : (z : Sphere) ∈ d.physicalDomain := heq ▸ p.property
      have hzx : π (z : Sphere) = x := heq ▸ hp
      rw [← hzx]
      exact finite_domain_point_avoided d hU hG π hπ hclosed hsurj hr he hend P g hg
        hocc henergy z hz

end CircleDomainRigidity

end

end OAI
