import OAI.Analysis.CircleDomains.Uniformization.FiniteUniformization

namespace OAI

/-!
# Nested target collars and complementary components

The end-component argument uses compactness twice: a nested sequence of
continua has connected intersection, and a connected subset of a finite
disjoint closed cover stays in the piece containing its initial point.
These are proved here for the actual target sphere. No uniformization or
boundary-extension statement is assumed.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem nested_sphere_sets_eventually_subset
    {C : ℕ → Set Sphere} (hclosed : ∀ n, IsClosed (C n))
    (hnest : Antitone C) {O : Set Sphere} (hO : IsOpen O)
    (hsub : (⋂ n, C n) ⊆ O) : ∃ n, C n ⊆ O := by
  obtain ⟨n, hn⟩ := hO.isClosed_compl.isCompact.elim_directed_family_closed C hclosed
    (disjoint_compl_left_iff_subset.mpr hsub) hnest.directed_ge
  exact ⟨n, disjoint_compl_left_iff_subset.mp hn⟩

theorem isConnected_nested_sphere_intersection
    {C : ℕ → Set Sphere} (hclosed : ∀ n, IsClosed (C n))
    (hconn : ∀ n, IsConnected (C n)) (hnest : Antitone C) :
    IsConnected (⋂ n, C n) := by
  refine ⟨IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n => hnest (Nat.le_succ n)) (fun n => (hconn n).nonempty)
    (hclosed 0).isCompact hclosed, ?_⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter hclosed)]
  intro a b ha hb hab hdisj
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := normal_separation ha hb hdisj
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset hclosed hnest (hu.union hv)
    (hab.trans (union_subset_union hau hbv))
  rcases (hconn n).isPreconnected.subset_or_subset hu hv huv hn with hn_u | hn_v
  · left
    exact Disjoint.left_le_of_le_sup_right hab
      (huv.mono ((iInter_subset C n).trans hn_u) hbv)
  · right
    exact (huv.symm.mono ((iInter_subset C n).trans hn_v) hau).left_le_of_le_sup_left hab

/-- A component of a subset of a finite disjoint closed union stays in
the unique piece that contains the chosen point. The pieces need not
themselves be connected. -/
theorem connectedComponentIn_subset_finite_closed_piece
    {I : Type*} [Finite I] {E : Set Sphere}
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hdisj : Pairwise (Disjoint on C)) (hcover : E ⊆ ⋃ i, C i)
    {i : I} {p : Sphere} (hp : p ∈ E) (hpi : p ∈ C i) :
    connectedComponentIn E p ⊆ C i := by
  classical
  let R : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    rintro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover' : E ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := E) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover')
      (by rw [hCR.inter_eq, inter_empty]) with h | h
  · exact h
  · exact fun _ _ => (Set.disjoint_left.mp hCR hpi (h (mem_connectedComponentIn hp))).elim

/-- The nested target disks for an end form exactly one complementary
component once the finite image cores give the closed covers. -/
theorem connectedComponentIn_eq_nested_end
    {I : ℕ → Type*} [∀ n, Finite (I n)] {E : Set Sphere}
    (C : (n : ℕ) → I n → Set Sphere) (b : (n : ℕ) → I n)
    (hclosed : ∀ n i, IsClosed (C n i))
    (hconn : ∀ n, IsConnected (C n (b n)))
    (hdisj : ∀ n, Pairwise (Disjoint on C n))
    (hcover : ∀ n, E ⊆ ⋃ i, C n i)
    (hnest : Antitone (fun n => C n (b n)))
    (hmiss : (⋂ n, C n (b n)) ⊆ E)
    {p : Sphere} (hp : p ∈ ⋂ n, C n (b n)) :
    connectedComponentIn E p = ⋂ n, C n (b n) := by
  apply Subset.antisymm
  · apply subset_iInter
    intro n
    exact connectedComponentIn_subset_finite_closed_piece (C n) (hclosed n)
      (hdisj n) (hcover n) (hmiss hp) (mem_iInter.mp hp n)
  · exact (isConnected_nested_sphere_intersection (fun n => hclosed n (b n)) hconn
      hnest).isPreconnected.subset_connectedComponentIn hp hmiss

/-- Strict nesting traps the limiting end inside every earlier collar. -/
theorem nested_end_subset_interior
    {C : ℕ → Set Sphere} (hstrict : ∀ n, C (n + 1) ⊆ interior (C n)) (n : ℕ) :
    (⋂ k, C k) ⊆ interior (C n) :=
  (iInter_subset C (n + 1)).trans (hstrict n)

end CircleDomainRigidity

end

end OAI
