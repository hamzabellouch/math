import OAI.Analysis.CircleDomains.Selection.SelectedMixedMeanExclusion
import OAI.Analysis.CircleDomains.Selection.SizedMeanExclusion

namespace OAI

/-! The open radius interval and the original mean exclusion survive the
restriction to the selected common marks. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem excludes_retained_sized_mean
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (A : AssignedMixedModelLimit F.model)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π)
    (l : I) {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness (D l).coordinate F₀ hF₀ c r R)
    (B : ℝ) (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * B) :
    ((finiteSourceMap A.function A.continuousOn,
      A.center ⟨(D l).coordinate.singular, F.singular l⟩,
      (⟨A.radius ⟨(D l).coordinate.singular, F.singular l⟩,
        (A.bounds _).2.1⟩ : ℝ≥0)), F.model.real.radius) ∉ W.sizedNeighborhood B := by
  intro hp
  have hR : 0 ≤ R := by
    have hpos := F.model.real.radius_pos
    have hupper := hp.2.2
    linarith
  let W' := W.restrictMarks F.marks (F.singular l) (F.support l) hR
  apply W'.not_mem_sizedNeighborhood hgreen hsch harea A hG hinf hπ hclosed rfl l
    HEq.rfl B hbound
  exact ⟨W.neighborhood_subset_restrictMarks F.marks (F.singular l) (F.support l) hR hp.1,
    hp.2⟩

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
