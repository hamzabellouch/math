import OAI.Analysis.CircleDomains.Selection.CountableUnavailableEndpoints
import OAI.Analysis.CircleDomains.Modulus.SelectedBarrierTest
import OAI.Analysis.CircleDomains.Selection.SelectedRealFamily

namespace OAI

/-! The greedy selection of tests misses only countably many ends at each
accuracy, by the positive-law recursion and alternating disk crossings. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def uncoveredTestEnds {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {EStar : Set Sphere} (A : Set (GradedRealTest d π EStar)) (k : ℕ) : Set Sphere :=
  {p | p ∈ d.dust ∧ ∀ b ∈ A, b.grade = k → p ∉ b.region}

theorem countable_uncovered_test_endpoints
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (P : Set Sphere) (hPB : P ⊆ d.dust)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set (GradedRealTest d π EStar)) (k : ℕ)
    (hmiss : ∀ p ∈ P, p ∈ uncoveredTestEnds A k)
    (hcover : ∀ b, GradedRealTest.Allowed A b → ∀ x ∈ b.toUngatedRealTest.openEnds,
      ∃ a ∈ A, a.grade = b.grade ∧ x ∈ a.toUngatedRealTest.openEnds)
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere)
    (hMc : M.Countable) (hMB : M ⊆ d.dust)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (hselected : ∀ a ∈ insert (UngatedRealTest.zeroTest d π EStar)
      (GradedRealTest.toUngatedRealTest '' A), ∃ i, c i = a)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M))
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    : P.Countable := by
  let e := realTestLevelData d c
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  apply countable_unavailable_endpoints hcross hcoarea hLusin hsard hsch
    e hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad hinf
    EStar hE hEU hEStar hEStarE hinfE P hPB D hnest hshrink hED hfiber harcs
    (realTestLevelData.previous c) (fun _ => rfl)
    (realTestLevelData.weight_finite c) (realTestLevelData.point_bound c hU hdense hBU)
    M hMc hMB (realTestLevelData.marked_weights c M hM) hcompat
    (realTestLevelData.unique_free_trace c hdense M hM) C hC hderiv
    hstandard hpath ω hω hωsum hdual hlift (ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (ENNReal.ofReal_pos.mpr hk)
  intro p R
  by_contra h
  have hsmall : R.controlledSize < ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    lt_of_not_ge h
  obtain ⟨b, hb, hbk, hbreg⟩ := GradedRealTest.exists_allowed_of_small_barrier
    c M hM A hselected (fun n => (D p n).isOpen_region hπ hclosed hsurj hr) R k hsmall
  have hpreg : p.val ∈ (D p R.level).region :=
    (D p R.level).point_mem_region hsurj (fun hp => hinfty (hp ▸ hPB p.property))
  have hpopen : (⟨p.val, hPB p.property⟩ : d.dust) ∈ b.toUngatedRealTest.openEnds := by
    change p.val ∈ b.region
    rwa [hbreg]
  obtain ⟨a, ha, hak, hpa⟩ := hcover b hb _ hpopen
  exact (hmiss p.val p.property).2 a ha (hak.trans hbk) hpa

end CircleDomainRigidity

end

end OAI
