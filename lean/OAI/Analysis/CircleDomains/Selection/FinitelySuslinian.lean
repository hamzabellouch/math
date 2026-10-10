import OAI.Analysis.CircleDomains.Topology.BoundaryBumping
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-!
# Finite bounds on disjoint continua imply local connectedness

This is the topological implication (ii) to (iii) in the generic-level
continua lemma of `047-02`, Section 1. Components of a closed ball that
meet its half-radius ball have uniformly positive diameter by boundary
bumping. There are only finitely many of them, so the component through
the center is a neighborhood of that center.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity

/-- A uniform finite bound on the number of pairwise disjoint subcontinua
having any fixed positive minimum diameter. -/
def HasFiniteLargeContinuumBound (X : Type*) [MetricSpace X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : Finset (Set X),
    (∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ ε ≤ diam C) →
    (∀ C ∈ S, ∀ D ∈ S, C ≠ D → Disjoint C D) → S.card ≤ N

/-- Finite total length gives a uniform cardinal bound when every continuum
of a fixed minimum diameter pays a positive amount of that length. The
geometric lower payment remains an explicit hypothesis. -/
theorem finite_large_continuum_bound_of_measure {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ]
    (hpayment : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C → δ ≤ μ.real C) :
    HasFiniteLargeContinuumBound X := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hpay⟩ := hpayment ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (μ.real univ / δ)
  refine ⟨N, ?_⟩
  intro S hS hdisj
  have hsum : (S.card : ℝ) * δ ≤ ∑ C ∈ S, μ.real C := by
    calc
      (S.card : ℝ) * δ = ∑ C ∈ S, δ := by simp
      _ ≤ ∑ C ∈ S, μ.real C :=
        Finset.sum_le_sum (fun C hC => hpay C (hS C hC).1 (hS C hC).2.1 (hS C hC).2.2)
  have htotal : (∑ C ∈ S, μ.real C) ≤ μ.real univ :=
    MeasureTheory.sum_measureReal_le_measureReal_univ
      (fun C hC => (hS C hC).1.isClosed.measurableSet) hdisj
  have hcard : (S.card : ℝ) ≤ μ.real univ / δ :=
    (le_div_iff₀ hδ).mpr (hsum.trans htotal)
  exact_mod_cast (hcard.trans_lt hN).le

private theorem finite_large_continuum_family {X : Type*} [MetricSpace X]
    (hbound : HasFiniteLargeContinuumBound X) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Set X)}
    (hS : ∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ ε ≤ diam C)
    (hdisj : S.Pairwise Disjoint) : S.Finite := by
  classical
  obtain ⟨N, hN⟩ := hbound ε hε
  by_contra hinf
  obtain ⟨T, hTS, hcard⟩ := (show S.Infinite from hinf).exists_subset_card_eq (N + 1)
  have hle := hN T (fun C hC => hS C (hTS hC))
    (fun C hC D hD hne => hdisj (hTS hC) (hTS hD) hne)
  omega

private theorem closed_componentIn {X : Type*} [TopologicalSpace X]
    {F : Set X} (hF : IsClosed F) (x : X) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- A disjoint family of nondegenerate subcontinua is countable: for each
positive reciprocal diameter threshold only finitely many can occur. -/
theorem countable_disjoint_nontrivial_subcontinua {X : Type*} [MetricSpace X]
    (hbound : HasFiniteLargeContinuumBound X) {S : Set (Set X)}
    (hS : ∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ C.Nontrivial)
    (hdisj : S.Pairwise Disjoint) : S.Countable := by
  let T : ℕ → Set (Set X) := fun n => {C ∈ S | 1 / ((n : ℝ) + 1) ≤ diam C}
  have hfinite (n : ℕ) : (T n).Finite :=
    finite_large_continuum_family hbound (by positivity)
      (fun C hC => ⟨(hS C hC.1).1, (hS C hC.1).2.1, hC.2⟩)
      (hdisj.mono (fun _ hC => hC.1))
  apply (Set.countable_iUnion (fun n => (hfinite n).countable)).mono
  intro C hC
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (diam_pos (hS C hC).2.2 (hS C hC).1.isBounded)
  exact mem_iUnion.mpr ⟨n, hC, hn.le⟩

/-- The nondegenerate connected components of a compact metric space are
countable under the finite-continuum bound. -/
theorem countable_nontrivial_connectedComponents {X : Type*} [MetricSpace X]
    [CompactSpace X] (hbound : HasFiniteLargeContinuumBound X) :
    {C : Set X | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable := by
  apply countable_disjoint_nontrivial_subcontinua hbound
  · rintro C ⟨⟨x, rfl⟩, hC⟩
    exact ⟨isClosed_connectedComponent.isCompact, isConnected_connectedComponent, hC⟩
  · rintro C ⟨⟨x, rfl⟩, hx⟩ D ⟨⟨y, rfl⟩, hy⟩ hne
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    exact hne ((connectedComponent_eq hxz).trans (connectedComponent_eq hyz).symm)

/-- The component of a closed ball through its center is a neighborhood
when the ambient continuum has finite bounds on large disjoint continua. -/
theorem closedBall_component_mem_nhds {X : Type*} [MetricSpace X]
    [CompactSpace X] [PreconnectedSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (x : X) {r : ℝ} (hr : 0 < r) :
    connectedComponentIn (closedBall x r) x ∈ 𝓝 x := by
  classical
  let F := closedBall x r
  let C₀ := connectedComponentIn F x
  by_cases hproper : F = univ
  · change C₀ ∈ 𝓝 x
    simp only [C₀, hproper, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
    exact univ_mem
  have hF : IsClosed F := isClosed_closedBall
  let S : Set (Set X) := {C | ∃ y ∈ ball x (r / 2), C = connectedComponentIn F y}
  have hyF {y : X} (hy : y ∈ ball x (r / 2)) : y ∈ F := by
    change dist y x ≤ r
    have hdist : dist y x < r / 2 := hy
    linarith
  have hS : ∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ r / 2 ≤ diam C := by
    rintro C ⟨y, hy, rfl⟩
    have hc : IsCompact (connectedComponentIn F y) := (closed_componentIn hF y).isCompact
    have hconn : IsConnected (connectedComponentIn F y) :=
      isConnected_connectedComponentIn_iff.mpr (hyF hy)
    obtain ⟨z, hzC, hzfront⟩ := component_meets_frontier hF hproper (hyF hy)
    have hzdist : dist z x = r := frontier_closedBall_subset_sphere hzfront
    have hyDist : dist y x < r / 2 := hy
    have hdiam := dist_le_diam_of_mem hc.isBounded hzC (mem_connectedComponentIn (hyF hy))
    have htri := dist_triangle z y x
    exact ⟨hc, hconn, by linarith⟩
  have hdisj : S.Pairwise Disjoint := by
    rintro C ⟨y, hy, rfl⟩ D ⟨z, hz, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro w hwy hwz
    exact hne ((connectedComponentIn_eq hwy).trans (connectedComponentIn_eq hwz).symm)
  have hSfinite : S.Finite := finite_large_continuum_family hbound (by positivity) hS hdisj
  let B : Set X := ⋃₀ (S \ {C₀})
  have hBclosed : IsClosed B :=
    hSfinite.sdiff.isClosed_sUnion (fun C hC => (hS C hC.1).1.isClosed)
  have hxnotB : x ∉ B := by
    rintro ⟨C, hC, hxC⟩
    have hne : C ≠ C₀ := by simpa using hC.2
    obtain ⟨y, hy, rfl⟩ := hC.1
    exact hne (connectedComponentIn_eq hxC)
  have hVnhds : ball x (r / 2) ∩ Bᶜ ∈ 𝓝 x :=
    inter_mem (ball_mem_nhds x (by positivity)) (hBclosed.isOpen_compl.mem_nhds hxnotB)
  apply Filter.mem_of_superset hVnhds
  rintro y ⟨hy, hyB⟩
  have hCy : connectedComponentIn F y ∈ S := ⟨y, hy, rfl⟩
  have hyelem := mem_connectedComponentIn (hyF hy)
  have heq : connectedComponentIn F y = C₀ := by
    by_contra hne
    apply hyB
    exact ⟨connectedComponentIn F y, ⟨hCy, by simpa using hne⟩, hyelem⟩
  change y ∈ C₀
  rwa [← heq]

/-- A compact metric continuum with uniform finite bounds on large
pairwise disjoint subcontinua is locally connected. -/
theorem locallyConnectedSpace_of_finite_large_continuum_bound
    {X : Type*} [MetricSpace X] [CompactSpace X] [PreconnectedSpace X]
    (hbound : HasFiniteLargeContinuumBound X) : LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hU
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  exact ⟨connectedComponentIn (closedBall x r) x,
    closedBall_component_mem_nhds hbound x hr, isPreconnected_connectedComponentIn,
    (connectedComponentIn_subset _ _).trans hsub⟩

/-- The finite bound is inherited by metric subspaces, with the same
bound on cardinalities. -/
theorem HasFiniteLargeContinuumBound.subtype {X : Type*} [MetricSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (K : Set X) :
    HasFiniteLargeContinuumBound K := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := hbound ε hε
  refine ⟨N, ?_⟩
  intro S hS hdisj
  let e : Set K → Set X := Set.image Subtype.val
  have he : Function.Injective e := Subtype.val_injective.image_injective
  have hiso : Isometry ((↑) : K → X) := fun _ _ => rfl
  have hle := hN (S.image e) (by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hc, hconn, hdiam⟩ := hS D hD
    refine ⟨hc.image continuous_subtype_val,
      hconn.image Subtype.val continuous_subtype_val.continuousOn, ?_⟩
    simpa only [e, hiso.diam_image] using hdiam) (by
    intro C hC D hD hne
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hD
    exact (Set.disjoint_image_iff Subtype.val_injective).mpr
      (hdisj C' hC' D' hD' (fun h => hne (congrArg e h))))
  rwa [Finset.card_image_of_injective S he] at hle

/-- In particular every compact connected subcontinuum is locally
connected under the ambient finite-continuum bound. -/
theorem locallyConnected_subcontinuum_of_finite_large_continuum_bound
    {X : Type*} [MetricSpace X] (hbound : HasFiniteLargeContinuumBound X)
    {K : Set X} (hK : IsCompact K) (hconn : IsConnected K) :
    LocallyConnectedSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : PreconnectedSpace K := Subtype.preconnectedSpace hconn.isPreconnected
  exact locallyConnectedSpace_of_finite_large_continuum_bound (hbound.subtype K)

end CircleDomainRigidity

end OAI
