import OAI.Analysis.CircleDomains.Probability.RecursiveLawContacts
import OAI.Analysis.CircleDomains.Probability.CountableQuotientCodeLaws

namespace OAI

/-! Applying the crossing countability theorem to the recursively retained
laws. The earlier-law lookup is the only ordering information required. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_recursive_code_laws {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust) (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hB : IsClosed base.dust) (hTD : IsTotallyDisconnected base.dust)
    (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hbad : ∀ x ∈ base.physicalDomainᶜ, π x ∈ base.dust)
    (hinf : π OnePoint.infty ∉ base.dust)
    (flags : Set Sphere) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : I → RecursiveCodeLaw base π flags ω)
    (hfinite : ∀ i, (L i).data.target ≠ OnePoint.infty)
    (hinj : Injective (fun i => (L i).data.target))
    (hprior : ∀ i j, i < j → ∃ n,
      (L j).data.priorLaws n = (codePathLaw (L i).data (L i).law : Measure C(PathTime, Sphere))) : Countable I := by
  let : ∀ i, IsFiniteMeasure (meanCodeOccupation (L i).data (L i).law) :=
    fun i => (L i).finite_occupation
  apply countable_quotient_code_laws hcross hcoarea hsard hsch
    base.physicalDomain base.quotientDomain base.dust base.anchor hG hU hdisj hBU hB hTD hE hEU
    π hπ hclosed hsurj hr hbad hinf (fun i => (L i).data)
    (fun i => (L i).physical_eq) (fun i => (L i).quotient_eq)
    (fun i => (L i).dust_eq) (fun i => (L i).anchor_eq)
    (fun i => (L i).domain_agrees) (fun i => ⟨(L i).target_dust, hfinite i⟩) hinj
    (fun i => (L i).law) (fun i => (L i).density) (fun i => (L i).density_measurable)
    (fun i => (L i).occupation_eq) (fun i => (L i).density_energy_finite)
    (fun i => (L i).hit_square_finite)
  intro i j hij
  obtain ⟨n, hn⟩ := hprior i j hij
  exact (L i).countable_contacts (L j) hB hflags hH hweights hmarked hcompat hunique n hn

end CircleDomainRigidity

end

end OAI
