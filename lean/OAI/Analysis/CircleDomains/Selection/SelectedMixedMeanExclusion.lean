import OAI.Analysis.CircleDomains.Transfer.SelectedMixedModels
import OAI.Analysis.CircleDomains.Selection.RestrictedMeanExclusion

namespace OAI

/-! The selected mixed model excludes each retained mean test on the same original
open neighborhood, after passing to the common countable set of marks. -/
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

 theorem excludes_retained_mean
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (A : AssignedMixedModelLimit F.model)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π)
    (l : I) {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness (D l).coordinate F₀ hF₀ c r R)
    (hsize : R = 5 * F.model.real.radius)
    (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * F.model.real.radius) :
    (finiteSourceMap A.function A.continuousOn,
      A.center ⟨(D l).coordinate.singular, F.singular l⟩,
      (⟨A.radius ⟨(D l).coordinate.singular, F.singular l⟩,
        (A.bounds _).2.1⟩ : ℝ≥0)) ∉ W.neighborhood := by
  have hR : 0 ≤ R := by rw [hsize]; exact mul_nonneg (by norm_num) F.model.real.radius_pos.le
  let W' := W.restrictMarks F.marks (F.singular l) (F.support l) hR
  have hnot := W'.not_mem_neighborhood hgreen hsch harea A hG hinf hπ hclosed rfl l
    HEq.rfl hsize hbound
  exact fun hp => hnot (W.neighborhood_subset_restrictMarks F.marks (F.singular l) (F.support l) hR hp)

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
