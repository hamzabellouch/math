import OAI.Analysis.CircleDomains.Selection.RealExclusionWitness
import OAI.Analysis.CircleDomains.Modulus.SelectableLevelBarrier

namespace OAI

/-! The actual small compatible barrier supplies both its selectable
coordinate and the open sized real exclusion carried into the final model. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem CompatibleLevelBarrier.exists_selectable_exclusion
    (hweighted : WeightedPlanarScalarCoarea)
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hπG : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain → π (z : Sphere) ∈ base.quotientDomain)
    (hpre : π ⁻¹' base.quotientDomain ⊆ base.physicalDomain)
    (hinf : π OnePoint.infty ∈ base.anchor)
    (p : base.dust)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} {E : RealTargetEnd A q}
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    {previous : PriorLevelFamily base.physicalDomain π} {flags EStar : Set Sphere}
    {regions : ℕ → Set Sphere} {f : base.quotientDomain → Sphere} {W₁ : Set Sphere}
    (R : CompatibleLevelBarrier base π previous flags EStar regions f W₁)
    (hregions : ∀ n, IsOpen (regions n)) (hqregions : ∀ n, π q ∈ regions n)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar)
    (hf : ∀ (z : ℂ) (hz : (z : Sphere) ∈ base.physicalDomain),
      f ⟨π (z : Sphere), hπG z hz⟩ = (A.function z : Sphere))
    (hW : ((↑) : ℂ → Sphere) '' closedBall T.center T.radius ⊆ W₁)
    (hsmall : R.controlledSize.toReal < T.selectionThreshold)
    (hinfty : π OnePoint.infty ∈ interior EStar)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c)) :
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      ∃ W : RealExclusionWitness base π c.coordinate,
        W.radius = T.selectionRadius ∧
        finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ W.neighborhood ∧
        ∀ a : ℂ, ∀ r : ℝ≥0,
          ((finiteSourceMap A.function (A.plane_open_embedding hG).1, a, r), M.radius) ∈
            W.sizedNeighborhood := by
  obtain ⟨c, hcomp, _, P, hP⟩ := exists_selectable_level_barrier hweighted base hU hG hdense
    π hπ he hB p previous flags EStar hinfty regions f W₁ R Candidates label hflags hgraphs
  obtain ⟨V, hV, hmem, hexclude⟩ := R.exists_open_exclusion_with_slack hsch harea hG hconn
    hπ hr hπG hpre hinf T hq hregions hqregions hzero hf hW hsmall
  let X : RealExclusionWitness base π c.coordinate := {
    presentation := P
    weight := R.weight
    weight_finite := R.weight_finite
    band_bound := by rw [hP]; exact R.band_bound
    radius := T.selectionRadius
    neighborhood := V
    isOpen_neighborhood := hV
    excludes := by
      intro S' π' σ' d' O' ε' M' A' l hG' hε hR hphysical hnorm
      apply hexclude M' A' l hε hR
      · rwa [← hP]
      · exact hnorm }
  refine ⟨c, hcomp, X, rfl, hmem, ?_⟩
  intro a r
  exact X.mem_sizedNeighborhood hmem T.model_lt_selectionRadius

end CircleDomainRigidity

end

end OAI
