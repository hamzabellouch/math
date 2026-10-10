import OAI.Analysis.CircleDomains.Modulus.HausdorffPayment
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-!
# Uniform crossing from a compact physical core

This supplies the geometric input to the length-payment argument in
the generic-level-continua lemma. A compact core inside the physical
domain has a uniform ball neighborhood there. Uniform continuity of
the quotient map makes these balls too small to contain a large
quotient continuum.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- A connected continuum covered off a core by disjoint open sets of
small diameter must meet that core. In the application the ambient
compact metric space is the level union itself. -/
theorem continuum_meets_core_of_small_open_cover
    {X ι : Type*} [MetricSpace X] [CompactSpace X]
    {F C : Set X} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (Disjoint on U)) (hcover : Fᶜ ⊆ ⋃ i, U i)
    {ε : ℝ} (hsmall : ∀ i, diam (U i) < ε)
    (hconn : IsConnected C) (hdiam : ε ≤ diam C) : (C ∩ F).Nonempty := by
  classical
  by_contra hmeet
  have hCU : C ⊆ ⋃ i, U i := by
    intro x hx
    apply hcover
    intro hxF
    exact hmeet ⟨x, hx, hxF⟩
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hCU hx)
  let V : Set X := ⋃ j : {j : ι // j ≠ i}, U j.val
  have hVopen : IsOpen V := isOpen_iUnion (fun j => hopen j.val)
  have hiV : Disjoint (U i) V := by
    apply disjoint_iUnion_right.mpr
    intro j
    exact hdisj j.property.symm
  have hunion : C ⊆ U i ∪ V := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hCU hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hCi := hconn.isPreconnected.subset_left_of_subset_union
    (hopen i) hVopen hiV hunion ⟨x, hx, hi⟩
  have hd : diam C ≤ diam (U i) :=
    diam_mono hCi (isCompact_univ.isBounded.subset (subset_univ _))
  exact (not_lt_of_ge (hdiam.trans hd)) (hsmall i)

/-- A compact physical core meeting every sufficiently large quotient
continuum supplies uniformly sized physical balls that those continua
must exit. -/
theorem uniform_ball_crossing_of_compact_core
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    {G K : Set Y} (hG : IsOpen G) (hK : IsCompact K) (hKG : K ⊆ G)
    {ε : ℝ} (hε : 0 < ε)
    (hcore : ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C →
      (C ∩ π '' K).Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∀ C : Set X,
      IsCompact C → IsConnected C → ε ≤ diam C →
      ∃ p ∈ π ⁻¹' C, closedBall p r ⊆ G ∧ ∃ q ∈ π ⁻¹' C, r < dist q p := by
  obtain ⟨ρ, hρ, hthick⟩ := hK.exists_cthickening_subset_open hG hKG
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hπ) (ε / 3) (by positivity)
  let r := min ρ (δ / 2)
  have hr : 0 < r := lt_min hρ (half_pos hδ)
  refine ⟨r, hr, ?_⟩
  intro C hcompact hconn hdiam
  obtain ⟨x, hxC, p, hpK, hpx⟩ := hcore C hcompact hconn hdiam
  have hpC : p ∈ π ⁻¹' C := by simpa only [mem_preimage, hpx] using hxC
  refine ⟨p, hpC, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (min_le_left ρ (δ / 2))).trans
      ((closedBall_subset_cthickening hpK ρ).trans hthick)
  · by_contra hno
    push Not at hno
    have hCball : C ⊆ closedBall (π p) (ε / 3) := by
      intro y hy
      obtain ⟨q, hq⟩ := hsurj y
      have hqC : q ∈ π ⁻¹' C := by simpa only [mem_preimage, hq] using hy
      have hqp : dist q p < δ :=
        (hno q hqC).trans_lt ((min_le_right ρ (δ / 2)).trans_lt (half_lt_self hδ))
      have hdist := hsmall hqp
      change dist y (π p) ≤ ε / 3
      exact hq ▸ hdist.le
    have hd := diam_le_of_subset_closedBall (by positivity : 0 ≤ ε / 3) hCball
    linarith

/-- Finite physical level length and arbitrarily fine compact cores give
the finite large-continuum bound in the quotient. The core-intersection
hypothesis is explicit; the radius choice, ball crossing, Hausdorff
payment, and cardinal estimate are all derived. -/
theorem finite_large_continuum_bound_of_compact_cores
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y} (hG : IsOpen G)
    (hlength : (μH[1] : Measure Y) G < ∞)
    (hcores : ∀ ε : ℝ, 0 < ε → ∃ K : Set Y,
      IsCompact K ∧ K ⊆ G ∧
      ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C →
        (C ∩ π '' K).Nonempty) : HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_quotient_length π hπ hsurj hfiber hlength
  intro ε hε
  obtain ⟨K, hK, hKG, hcore⟩ := hcores ε hε
  exact uniform_ball_crossing_of_compact_core π hπ hsurj hG hK hKG hε hcore

/-- The form used for generic level unions: outside a compact physical
core, the quotient is covered by disjoint relatively open dust disks of
arbitrarily small diameter. Finite physical length then bounds the
number of disjoint large subcontinua. -/
theorem finite_large_continuum_bound_of_small_open_core_covers
    {X Y ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y} (hG : IsOpen G)
    (hlength : (μH[1] : Measure Y) G < ∞)
    (hcovers : ∀ ε : ℝ, 0 < ε → ∃ (K : Set Y) (U : ι → Set X),
      IsCompact K ∧ K ⊆ G ∧ (∀ i, IsOpen (U i)) ∧
      Pairwise (Disjoint on U) ∧ (π '' K)ᶜ ⊆ ⋃ i, U i ∧ ∀ i, diam (U i) < ε) :
    HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_compact_cores π hπ hsurj hfiber hG hlength
  intro ε hε
  obtain ⟨K, U, hK, hKG, hopen, hdisj, hcover, hsmall⟩ := hcovers ε hε
  refine ⟨K, hK, hKG, ?_⟩
  intro C _ hconn hdiam
  exact continuum_meets_core_of_small_open_cover U hopen hdisj hcover hsmall hconn hdiam

end CircleDomainRigidity

end OAI
