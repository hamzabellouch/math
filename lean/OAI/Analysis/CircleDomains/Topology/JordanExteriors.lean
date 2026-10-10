import OAI.Analysis.CircleDomains.Selection.OuterContours
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.Separation.DisjointCover

namespace OAI

/-!
# The common exterior of finitely many disjoint Jordan disks

Removing finitely many disjoint closed Jordan disks leaves a preconnected
set. We first prove the closed-complement version by extending any separation
across disks according to which side contains their connected boundaries.
Small enlargements of the disks then give the open-complement version.
These are proved topology lemmas, not additional published inputs.
-/

open Set Filter Function Metric
open scoped Topology

namespace CircleDomainRigidity

/-- Fill connected boundary components into either side of a hypothetical
separation. Finiteness makes both enlarged sides closed. -/
theorem isPreconnected_compl_finite_open_disks
    {X I : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Finite I]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hfront : ∀ i, IsPreconnected (frontier (U i)))
    (hdisj : Pairwise (Disjoint on fun i => closure (U i))) :
    IsPreconnected (⋃ i, U i)ᶜ := by
  classical
  let C : Set X := (⋃ i, U i)ᶜ
  have hC : IsClosed C := (isOpen_iUnion hU).isClosed_compl
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hC).mpr
  intro A B hA hB hcover hAB
  let A₀ := A ∩ C
  let B₀ := B ∩ C
  have hfrontC (i : I) : frontier (U i) ⊆ C := by
    intro x hx hxU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
    by_cases hij : i = j
    · subst j
      rw [(hU i).frontier_eq] at hx
      exact hx.2 hj
    · exact Set.disjoint_left.mp (hdisj hij) (frontier_subset_closure hx)
        (subset_closure hj)
  have hchoice (i : I) : frontier (U i) ⊆ A₀ ∨ frontier (U i) ⊆ B₀ := by
    apply (isPreconnected_iff_subset_of_disjoint_closed.mp (hfront i)) A₀ B₀
      (hA.inter hC) (hB.inter hC)
    · intro x hx
      exact (hcover (hfrontC i hx)).imp (fun h => ⟨h, hfrontC i hx⟩)
        (fun h => ⟨h, hfrontC i hx⟩)
    · apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨_, hxA, hxB⟩
      exact Set.disjoint_left.mp hAB hxA.1 hxB.1
  let P : Set I := {i | frontier (U i) ⊆ A₀}
  have hBfront (i : I) (hi : i ∉ P) : frontier (U i) ⊆ B₀ :=
    (hchoice i).resolve_left hi
  let A' := A₀ ∪ ⋃ i ∈ P, closure (U i)
  let B' := B₀ ∪ ⋃ i ∈ Pᶜ, closure (U i)
  have hA' : IsClosed A' := (hA.inter hC).union
    (P.toFinite.isClosed_biUnion (fun _ _ => isClosed_closure))
  have hB' : IsClosed B' := (hB.inter hC).union
    (Pᶜ.toFinite.isClosed_biUnion (fun _ _ => isClosed_closure))
  have hclC (i : I) : closure (U i) ∩ C ⊆ frontier (U i) := by
    intro x hx
    rw [frontier, (hU i).interior_eq]
    exact ⟨hx.1, fun hxU => hx.2 (mem_iUnion.mpr ⟨i, hxU⟩)⟩
  have hA'B' : Disjoint A' B' := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    rcases hxA with hxA | hxA <;> rcases hxB with hxB | hxB
    · exact Set.disjoint_left.mp hAB hxA.1 hxB.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      exact Set.disjoint_left.mp hAB hxA.1 (hBfront i hi (hclC i ⟨hxi, hxA.2⟩)).1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxA
      exact Set.disjoint_left.mp hAB (hi (hclC i ⟨hxi, hxB.2⟩)).1 hxB.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxA
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxB
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      exact Set.disjoint_left.mp (hdisj hij) hxi hxj
  have htotal : (univ : Set X) ⊆ A' ∪ B' := by
    intro x _
    by_cases hx : x ∈ C
    · exact (hcover hx).imp (fun h => Or.inl ⟨h, hx⟩) (fun h => Or.inl ⟨h, hx⟩)
    · have hxU : x ∈ ⋃ i, U i := by simpa only [C, mem_compl_iff, not_not] using hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      by_cases hiP : i ∈ P
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i, hiP, subset_closure hi⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨i, hiP, subset_closure hi⟩))
  have hside := (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_univ).mp
    isPreconnected_univ A' B' hA' hB' htotal hA'B'
  rcases hside with hside | hside
  · left
    intro x hx
    rcases hside (mem_univ x) with hxA | hxA
    · exact hxA.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxA
      exact (hi (hclC i ⟨hxi, hx⟩)).1
  · right
    intro x hx
    rcases hside (mem_univ x) with hxB | hxB
    · exact hxB.1
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      exact (hBfront i hi (hclC i ⟨hxi, hx⟩)).1

/-- Enlarge finitely many disjoint closed Jordan disks within prescribed
open neighborhoods, keeping their closures disjoint. -/
theorem exists_disjoint_jordan_enlargements
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (O : I → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hsub : ∀ i, closure (jordanInterior (H i)) ⊆ O i) :
    ∃ r : I → ℝ, (∀ i, 1 < r i) ∧
      (∀ i, H i '' closedBall (0 : ℂ) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => H i '' closedBall (0 : ℂ) (r i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (closure (jordanInterior (H i)))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_closure isClosed_closure (hdisj hij)
  obtain ⟨V, hV, hVdisj⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (closure (jordanInterior (H i))))
  have hex (i : I) : ∃ r : ℝ, 1 < r ∧
      H i '' closedBall (0 : ℂ) r ⊆ V i ∩ O i := by
    have hopen : IsOpen ((H i) ⁻¹' (V i ∩ O i)) :=
      ((hV i).1.inter (hO i)).preimage (H i).continuous
    have hcontain : closedBall (0 : ℂ) 1 ⊆ (H i) ⁻¹' (V i ∩ O i) := by
      intro x hx
      have hx' : H i x ∈ closure (jordanInterior (H i)) := by
        rw [closure_jordanInterior]
        exact mem_image_of_mem _ hx
      exact ⟨(hV i).2 hx', hsub i hx'⟩
    obtain ⟨δ, hδ, hδsub⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hopen hcontain
    refine ⟨δ + 1, by linarith, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply hδsub
    simpa only [cthickening_closedBall hδ.le zero_le_one] using hx
  choose r hr hrsub using hex
  refine ⟨r, hr, fun i x hx => (hrsub i hx).2, ?_⟩
  intro i j hij
  exact (hVdisj hij).mono (fun x hx => (hrsub i hx).1)
    (fun x hx => (hrsub j hx).1)

/-- Any two points outside the closed disks remain in the connected
complement of a sufficiently small simultaneous enlargement. -/
theorem isPreconnected_exterior_finite_jordanInteriors
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsPreconnected (⋃ i, closure (jordanInterior (H i)))ᶜ := by
  classical
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  let O : Set ℂ := ({x, y} : Set ℂ)ᶜ
  have hO : IsOpen O := ((Set.finite_singleton y).insert x).isClosed.isOpen_compl
  have hsub (i : I) : closure (jordanInterior (H i)) ⊆ O := by
    intro z hz hzxy
    rcases hzxy with rfl | hzxy
    · exact hx (mem_iUnion.mpr ⟨i, hz⟩)
    · have hzy : z = y := mem_singleton_iff.mp hzxy
      subst z
      exact hy (mem_iUnion.mpr ⟨i, hz⟩)
  obtain ⟨r, hr, hrsub, hrdisj⟩ :=
    exists_disjoint_jordan_enlargements H hdisj (fun _ => O) (fun _ => hO) hsub
  let U : I → Set ℂ := fun i => H i '' ball (0 : ℂ) (r i)
  have hUopen (i : I) : IsOpen (U i) := (H i).isOpenMap _ isOpen_ball
  have hUcl (i : I) : closure (U i) = H i '' closedBall (0 : ℂ) (r i) := by
    change closure (H i '' ball (0 : ℂ) (r i)) = _
    rw [← (H i).image_closure, closure_ball _ (by linarith [hr i])]
  have hUfront (i : I) : IsPreconnected (frontier (U i)) := by
    change IsPreconnected (frontier (H i '' ball (0 : ℂ) (r i)))
    rw [← (H i).image_frontier, frontier_ball _ (by linarith [hr i])]
    exact ((isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num)
      (0 : ℂ) (by linarith [hr i])).image (H i) (H i).continuous.continuousOn).isPreconnected
  have hUd : Pairwise (Disjoint on fun i => closure (U i)) := by
    intro i j hij
    simpa only [hUcl] using hrdisj hij
  refine ⟨(⋃ i, U i)ᶜ, ?_, ?_, ?_,
    isPreconnected_compl_finite_open_disks U hUopen hUfront hUd⟩
  · intro z hz hzcl
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzcl
    rw [closure_jordanInterior] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    apply hz
    exact mem_iUnion.mpr ⟨i, w, (closedBall_subset_ball (hr i)) hw, rfl⟩
  · intro hxU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    have hxO := hrsub i (hUcl i ▸ subset_closure hi)
    exact hxO (by simp)
  · intro hyU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyU
    have hyO := hrsub i (hUcl i ▸ subset_closure hi)
    exact hyO (by simp)

/-- A bounded open set cannot occupy the common exterior when its boundary
is covered by finitely many disjoint closed Jordan disks. -/
theorem open_subset_finite_jordan_fills_of_frontier_subset
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {U : Set ℂ} (hU : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hfront : frontier U ⊆ ⋃ i, closure (jordanInterior (H i))) :
    U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
  let K : Set ℂ := ⋃ i, closure (jordanInterior (H i))
  have hKbdd : Bornology.IsBounded K :=
    (isCompact_iUnion (fun i => isCompact_closure_jordanInterior (H i))).isBounded
  have hS := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hsplit : Kᶜ ⊆ U ∨ Kᶜ ⊆ (closure U)ᶜ := by
    apply hS.subset_or_subset hU isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
    · intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · right
        intro hzcl
        have hzfront : z ∈ frontier U := by
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
        exact hz (hfront hzfront)
  rcases hsplit with hin | hout
  · have hbad := hKbdd.union (hUbdd.subset hin)
    rw [union_compl_self] at hbad
    exact (NormedSpace.unbounded_univ ℝ ℂ hbad).elim
  · intro z hzU
    by_contra hzK
    exact hout hzK (subset_closure hzU)

/-- If the selected contours are themselves boundary curves of the open
set, coverage by closed fills is coverage by their interiors. -/
theorem open_subset_finite_jordanInteriors_of_frontier_subset
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {U : Set ℂ} (hU : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)))
    (hselected : ∀ i, frontier (jordanInterior (H i)) ⊆ frontier U) :
    U ⊆ ⋃ i, jordanInterior (H i) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp
    (open_subset_finite_jordan_fills_of_frontier_subset H hdisj hU hUbdd hcover hx)
  refine mem_iUnion.mpr ⟨i, ?_⟩
  by_contra hxi
  have hxfront : x ∈ frontier (jordanInterior (H i)) := by
    rw [(jordanInterior_isOpen (H i)).frontier_eq]
    exact ⟨hi, hxi⟩
  have hxf := hselected i hxfront
  rw [hU.frontier_eq] at hxf
  exact hxf.2 hx

end CircleDomainRigidity

end OAI
