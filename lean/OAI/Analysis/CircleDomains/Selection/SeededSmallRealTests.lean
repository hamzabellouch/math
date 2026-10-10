import OAI.Analysis.CircleDomains.Selection.CountableUncoveredSeededEnds
import OAI.Analysis.CircleDomains.Selection.FiniteSeededRealFamily

namespace OAI

/-! The actual graded selection gives one countable family, with only
countably many marked or uncovered ends across all accuracies. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_countable_small_real_tests_with_seed
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
    (_hBimage : d.dust = π '' d.physicalDomainᶜ)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : d.dust, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : d.dust, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
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
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (hzero : seed 0 = UngatedRealTest.zeroTest d π EStar)
    (hseed : ∀ (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1)),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (seed i).exclusions)
          (circleBandGraph d.quotientDomain (seed j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (seed i).coordinate.quotient) labels) = 0)
    : ∃ (A : Set (GradedRealTest d π EStar)) (c : ℕ → UngatedRealTest d π EStar)
        (M : Set Sphere), M.Countable ∧ M ⊆ d.dust ∧ c 0 = UngatedRealTest.zeroTest d π EStar ∧
      (∀ i : Fin (m + 1), c i.val = seed i) ∧
      (∀ i, (c i).exclusions ∩ d.dust ⊆ M) ∧
      (∀ b ∈ A, ∃ i, c i = b.toUngatedRealTest) ∧
      OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M) ∧
      ∀ p ∈ d.dust \ M, ∀ k, ∃ b ∈ A, b.grade = k ∧ p ∈ b.region := by
  classical
  obtain ⟨A, hA0, _, hmono, hsingle, hnew, _, hcover⟩ :=
    GradedRealTest.exists_countable_selection_with (range seed)
  obtain ⟨c, M, hMc, hMB, hc0, hprefix, hM, hselected, _, hcompat⟩ :=
    exists_finite_seeded_real_family d seed hzero hseed A hA0 hmono hsingle hnew
  have hselected' : range seed ∪ GradedRealTest.toUngatedRealTest '' (⋃ n, A n) ⊆
      range c := by
    intro a ha
    rcases ha with ⟨i, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨i.val, hprefix i⟩
    · exact hselected b hb
  have hcover' : ∀ b : GradedRealTest d π EStar,
      b.toUngatedRealTest.CompatibleWith (range c) →
      ∀ x ∈ b.toUngatedRealTest.openEnds,
        ∃ a ∈ ⋃ n, A n, a.grade = b.grade ∧ x ∈ a.toUngatedRealTest.openEnds := by
    intro b hb
    exact hcover b (hb.mono hselected')
  have hcount (k : ℕ) : (uncoveredTestEnds (⋃ n, A n) k).Countable := by
    apply countable_uncovered_test_endpoints_of_range hcross hcoarea hLusin hsard hsch
      d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad hinf
      EStar hE hEU hEStar hEStarE hinfE (uncoveredTestEnds (⋃ n, A n) k)
      (fun _ hp => hp.1) (fun p => D ⟨p.val, p.property.1⟩)
      (fun p => hnest ⟨p.val, p.property.1⟩)
      (fun p => hshrink ⟨p.val, p.property.1⟩)
      (fun p => hED ⟨p.val, p.property.1⟩) hfiber harcs
      (⋃ n, A n) k (fun _ hp => hp) c M hcover' hMc hMB hM hcompat
      C hC hderiv hstandard hpath ω hω hωsum hdual hlift
  let N : Set Sphere := M ∪ ⋃ k, uncoveredTestEnds (⋃ n, A n) k
  have hMN : M ⊆ N := subset_union_left
  have hNB : N ⊆ d.dust := by
    intro p hp
    rcases hp with hp | hp
    · exact hMB hp
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hp
      exact hk.1
  refine ⟨⋃ n, A n, c, N, hMc.union (countable_iUnion hcount), hNB, hc0, hprefix,
    (fun i => (hM i).trans hMN), hselected, hcompat.mono ?_, ?_⟩
  · intro p hp
    exact ⟨hp.1, fun h => hp.2 (hMN h)⟩
  · intro p hp k
    by_contra h
    apply hp.2
    right
    apply mem_iUnion.mpr
    refine ⟨k, hp.1, ?_⟩
    intro b hb hbk hpb
    exact h ⟨b, hb, hbk, hpb⟩

end CircleDomainRigidity

end

end OAI
