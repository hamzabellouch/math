import OAI.Analysis.CircleDomains.Topology.NestedCollarMeanExclusion
import OAI.Analysis.CircleDomains.Selection.ProtrusionGateGeometry
import OAI.Analysis.CircleDomains.Modulus.NormalizedSourceRepresentative

namespace OAI

/-! The actual marked-component protrusion and its recursive law produce
an inner mean exclusion. All map regularity and distance hypotheses are
derived from the conformal limit and the separated protrusion balls. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.eventually_protrusion_mean
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hp : L.data.target ≠ π OnePoint.infty)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {R : ℝ} (hR : 0 ≤ R)
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ,
      ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
      ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate)) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)),
        EqOn F₀ A.function (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain) ∧
        ∃ B : ℝ≥0, ∀ᶠ n in atTop,
          ∃ J : ℂ ≃ₜ ℂ, (D n).region = ((↑) : ℂ → Sphere) '' jordanInterior J ∧
          ∃ Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
            (meanBudgetTolerance B R (δ / 4)),
            Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ (A.center s)
              ⟨A.radius s, (A.bounds s).2.1⟩ R (δ / 4)) := by
  obtain ⟨δ, hδ, hgap⟩ := T.uniform_gate_gap hseparated
  obtain ⟨F₀, hF₀m, hF₀s, hEq⟩ := exists_normalized_source_representative hG A.function A.conformal.1
  have hf := quotientNormalizedMap_continuous base.domainEquiv A.function A.conformal.1
  have hmap := quotientNormalizedMap_eq_of_eqOn base.domainEquiv hEq
  have hgate : ∀ x : base.quotientDomain,
      quotientNormalizedMap base.domainEquiv A.function x ∈ closure T.openGate →
      quotientNormalizedMap base.domainEquiv A.function x =
        (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere) := by
    rw [← hmap]
    exact quotientNormalizedMap_finite_gate base.domainEquiv F₀ base.basePoint
      T.infinity_notMem_closure_openGate
  have hout : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain →
      A.radius s < dist (F₀ z) (A.center s) := by
    intro z hz
    rw [hEq hz]
    exact E.source_outside_marked_disk hr hq hqs z hz
  refine ⟨δ, hδ, F₀, hF₀s.continuousOn, hEq, ?_⟩
  exact L.eventually_gated_collar_mean hsch hsep hcoarea hcollar hselect harcs hG hU
    hdense hdust hπ hclosed hsurj hr he hbad hp D hnest hshrink hanchor hfinite hcontours
    (quotientNormalizedMap base.domainEquiv A.function) hf T.openGate hgates F₀
    hF₀s.continuousOn hF₀m hF₀s hgate (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩
    hout hR hδ hgap

end CircleDomainRigidity

end

end OAI
