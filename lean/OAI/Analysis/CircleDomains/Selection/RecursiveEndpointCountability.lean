import OAI.Analysis.CircleDomains.Probability.RecursiveLawSelection
import OAI.Analysis.CircleDomains.Probability.CountableRecursiveLaws

namespace OAI

/-! The first uncountable recursion and the actual crossing estimate exclude
uncountably many endpoints admitting the recursive positive-law selection. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_endpoints_of_recursive_selection
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
    (S : Set Sphere) (hS : S ⊆ base.dust \ {OnePoint.infty})
    (hselect : ∀ (p : Sphere), p ∈ S → ∀ (μ : ℕ → Measure C(PathTime, Sphere)),
      (∀ n, IsFiniteMeasure (μ n)) →
      (∀ n, (support (priorHitMass (μ n))).Countable) →
      ∃ L : RecursiveCodeLaw base π flags ω,
        L.data.target = p ∧ L.data.priorLaws = μ) : S.Countable := by
  by_contra hunc
  obtain ⟨p, hp, hpS⟩ := exists_injective_firstUncountable S hunc
  obtain ⟨L, htarget, hprior⟩ := exists_recursive_code_laws base π flags ω p
    (fun L => L.full_hit_support_countable hU hG hBU hdisj hπ hclosed hsurj hr)
    (fun i μ hf hμ => hselect (p i) (hpS (mem_range_self i)) μ hf hμ)
  have hc : Countable FirstUncountable := countable_recursive_code_laws
    hcross hcoarea hsard hsch base π hG hU hdisj hBU hB hTD hE hEU
    hπ hclosed hsurj hr hbad hinf flags hflags hH hweights hmarked hcompat hunique ω L
    (fun i => by rw [htarget i]; exact (hS (hpS (mem_range_self i))).2)
    (by intro i j hij; apply hp; simpa only [htarget] using hij) hprior
  exact firstUncountable_not_countable hc

end CircleDomainRigidity

end

end OAI
