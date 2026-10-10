import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.SelectedMixedModels
import OAI.Analysis.CircleDomains.Selection.SeededLevelPresentations

namespace OAI

/-! Open selection with its inherited ordering and common mixed
finite models. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selected_mixed_selection
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hinfty : OnePoint.infty ∈ base.physicalDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hTD : IsTotallyDisconnected base.dust) (hUB : Disjoint base.quotientDomain base.dust)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (hzero : (seed 0).coordinate.graph = circleBandGraph base.quotientDomain (fun _ => 0))
    (hseed : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
          (fun k => (seed k).coordinate.graph) labels) = 0)
    {T X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (data : T → SelectableMaskedCoordinate base π)
    (presentation : ∀ t, SelectedLevelPresentation hsch base π (data t).coordinate)
    (V : T → Set X) (hV : ∀ t, IsOpen (V t))
    (B₀ : Set base.dust) (hB₀ : B₀.Countable) :
    ∃ (A : ℕ → Set T) (q : ℕ → Option T),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧ (⋃ n, A n).Countable ∧
      (∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n) ∧
      (∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c) ∧
      (∀ c, seededMaskedAllowed seed data (⋃ n, A n) c →
        V c ⊆ ⋃ t ∈ ⋃ n, A n, V t) ∧
      (let D := orderedSelectedCoordinates seed data q
       ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
         (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
           (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
             (fun k => (D k).coordinate.graph) labels) = 0) ∧
      Nonempty (SelectedMixedModels hsch base hU hdense π he hB
        (orderedSelectedCoordinates seed data q)
        (orderedSelectedPresentations seed seedPresentation data presentation q) B₀) := by
  let : Countable (ℕ ⊕ₗ ℕ) := Function.Injective.countable
    (show Injective (ofLex : (ℕ ⊕ₗ ℕ) → ℕ ⊕ ℕ) from fun _ _ h => by
      simpa only [toLex_ofLex] using congrArg toLex h)
  obtain ⟨A, q, hA0, hfin, hmono, hcount, hq, hpref, hcover, _, hcompat⟩ :=
    exists_seeded_masked_selection seed hzero hseed data V hV
  refine ⟨A, q, hA0, hfin, hmono, hcount, hq, hpref, hcover, hcompat, ?_⟩
  exact exists_selected_mixed_models hsard hsch hcompact hfinite base hU hG hconn
    hinfty hdense π hπ hclosed hsurj hr he hB hTD hUB
    (orderedSelectedCoordinates seed data q)
    (orderedSelectedPresentations seed seedPresentation data presentation q)
    (orderedSelectedPresentations_infinite_real seed seedPresentation data presentation q)
    hcompat B₀ hB₀

end CircleDomainRigidity

end

end OAI
