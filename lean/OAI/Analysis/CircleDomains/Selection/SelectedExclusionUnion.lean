import OAI.Analysis.CircleDomains.Selection.CoordinateExclusionTest
import OAI.Analysis.CircleDomains.Selection.SeededLevelPresentations

namespace OAI

/-! Every neighborhood chosen by the actual ordered selection is excluded
by its common mixed limit, with its original component label retained. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem selected_limit_avoids_test_union
    {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
    {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
    {π : Sphere → Sphere}
    {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
    {hB : base.dust = π '' base.physicalDomainᶜ}
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    {B₀ : Set base.dust} {B : ℝ}
    (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ B))
    (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ B))
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (F : SelectedMixedModels hsch base hU hdense π he hB
      (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
      (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q) B₀)
    (A : AssignedMixedModelLimit F.model)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) :
    ∀ p : B₀,
      (p, (finiteSourceMap A.function A.continuousOn,
        A.center ⟨p.val, F.mandatory p.property⟩,
        (⟨A.radius ⟨p.val, F.mandatory p.property⟩, (A.bounds _).2.1⟩ : ℝ≥0)),
          F.model.real.radius) ∉ ⋃ t ∈ ⋃ n, S n, t.neighborhood := by
  intro p hx
  obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp ht
  obtain ⟨k, _, hk⟩ := (hpref n t).mp hn
  have hp : p = t.mark := (mem_singleton_iff.mp hx.1)
  subst p
  apply t.excludes_retained F A hgreen harea hG hinf hπ hclosed (Sum.inrₗ k) _ _ hx
  · simp only [orderedSelectedCoordinates, ofLex_toLex, hk, Option.elim_some]
  · exact orderedSelectedPresentations_some seed seedPresentation
      CoordinateExclusionTest.coordinate CoordinateExclusionTest.presentation q k t hk

end CircleDomainRigidity

end

end OAI
