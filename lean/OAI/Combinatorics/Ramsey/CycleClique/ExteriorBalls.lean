import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CycleShortening
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorPaths
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.IndependenceTwo
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem closedNeighborhood_mono {V : Type*} (G : SimpleGraph V) {A B : Set V}
    (h : A ⊆ B) : closedNeighborhood G A ⊆ closedNeighborhood G B := by
  rintro v (hv | ⟨u, hu, huv⟩)
  · exact Or.inl (h hv)
  · exact Or.inr ⟨u, h hu, huv⟩

theorem outside_neighborhood_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X Z A : Set V} {x : V} {r : ℕ}
    (hA : A ⊆ outsideBall G X x r) (hZ : Z ⊆ X)
    (hmiss : ∀ u ∈ A, ∀ z ∈ Z, ¬ G.Adj u z) :
    (closedNeighborhood G A).ncard + Z.ncard ≤
      X.ncard + (outsideBall G X x (r + 1)).ncard := by
  have hdis : Disjoint (closedNeighborhood G A) Z := by
    apply Set.disjoint_left.mpr
    rintro z (hz | ⟨u, hu, huz⟩) hzZ
    · exact outsideBall_subset_compl G X x r (hA hz) (hZ hzZ)
    · exact hmiss u hu z hzZ huz
  have hs : closedNeighborhood G A ⊆ outsideBall G X x (r + 1) ∪ (X \ Z) := by
    intro z hz
    rcases closedNeighborhood_ball_subset G X x r (closedNeighborhood_mono G hA hz) with hb | hx
    · exact Or.inl hb
    · exact Or.inr ⟨hx, fun hzZ => Set.disjoint_left.mp hdis hz hzZ⟩
  have hc := Set.ncard_le_ncard hs
  have hu := Set.ncard_union_le (outsideBall G X x (r + 1)) (X \ Z)
  have hd := Set.ncard_sdiff_add_ncard_of_subset hZ
  omega

theorem outsideBall_nonempty {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X : Set V} {x : V} {k : ℕ}
    (hx : x ∈ X) (hX : X.ncard ≤ k)
    (hdeg : k + 1 ≤ (closedNeighborhood G {x}).ncard) :
    (outsideBall G X x 0).Nonempty := by
  by_contra hn
  have hs : closedNeighborhood G {x} ⊆ X := by
    rintro v (hv | ⟨u, hu, huv⟩)
    · simpa using (Set.mem_singleton_iff.mp hv ▸ hx)
    · have he : u = x := hu
      subst u
      by_contra hvX
      exact hn ⟨v, huv, hvX⟩
  have hh := Set.ncard_le_ncard hs
  omega

theorem outsideBall_degree_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X Z : Set V} {x : V} {k : ℕ}
    (hx : x ∈ X) (hX : X.ncard ≤ k) (hZ : Z ⊆ X)
    (hdeg : ∀ u, k + 1 ≤ (closedNeighborhood G {u}).ncard)
    (hmiss : ∀ u ∈ outsideBall G X x 0, ∀ z ∈ Z, ¬ G.Adj u z) :
    k + 1 + Z.ncard ≤ X.ncard + (outsideBall G X x 1).ncard := by
  obtain ⟨u, hu⟩ := outsideBall_nonempty hx hX (hdeg x)
  have hc := outside_neighborhood_bound (Set.singleton_subset_iff.mpr hu) hZ
    (by intro v hv; have he : v = u := hv; subst v; exact hmiss u hu)
  have hd := hdeg u
  change (closedNeighborhood G {u}).ncard + Z.ncard ≤ X.ncard + (outsideBall G X x 1).ncard at hc
  omega

theorem outsideBall_independent_pair {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X R : Set V} {x : V} {k t : ℕ}
    (hR : R ⊆ X) (hx : x ∈ R) (hcardR : R.ncard = t) (hX : X.ncard ≤ k)
    (hclique : G.cliqueNum ≤ t)
    (hdeg : ∀ u, k + 1 ≤ (closedNeighborhood G {u}).ncard)
    (hmiss : ∀ u ∈ outsideBall G X x 1, ∀ z ∈ R \ {x}, ¬ G.Adj u z) :
    2 ≤ independence G (outsideBall G X x 2) := by
  have ht : 1 ≤ t := by
    have hp := (Set.ncard_pos).mpr (show R.Nonempty from ⟨x, hx⟩)
    omega
  have hZ : R \ {x} ⊆ X := Set.sdiff_subset.trans hR
  have hcZ : (R \ {x}).ncard = t - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hx, hcardR]
  have hb := outsideBall_degree_bound (hR hx) hX hZ hdeg
    (fun u hu => hmiss u (outsideBall_subset_succ G X x 0 hu))
  rw [hcZ] at hb
  by_contra hn
  have htwo : G.IsClique (outsideBall G X x 2) := clique_of_independence_le_one (by omega)
  have hc2 := (clique_ncard_le_cliqueNum htwo).trans hclique
  have hsub := outsideBall_subset_succ G X x 1
  have hc12 : (outsideBall G X x 1).ncard ≤ (outsideBall G X x 2).ncard := Set.ncard_le_ncard hsub
  have hc1 : (outsideBall G X x 1).ncard = t := by omega
  have hadj : ∀ z ∈ outsideBall G X x 1, G.Adj x z := by
    intro z hz
    by_contra hneg
    have hmissR : ∀ u ∈ ({z} : Set V), ∀ w ∈ R, ¬ G.Adj u w := by
      intro u hu w hw huw
      have he : u = z := hu
      subst u
      by_cases hwx : w = x
      · subst w
        exact hneg huw.symm
      · exact hmiss z hz w ⟨hw, hwx⟩ huw
    have hh := outside_neighborhood_bound (Set.singleton_subset_iff.mpr hz) hR hmissR
    rw [hcardR] at hh
    change (closedNeighborhood G {z}).ncard + t ≤ X.ncard + (outsideBall G X x 2).ncard at hh
    have hd := hdeg z
    omega
  have hxB : x ∉ outsideBall G X x 1 := fun hh =>
    outsideBall_subset_compl G X x 1 hh (hR hx)
  have hbig : G.IsClique (insert x (outsideBall G X x 1)) := by
    intro u hu v hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (huv rfl).elim
    · exact hadj v hv
    · exact (hadj u hu).symm
    · exact htwo (hsub hu) (hsub hv) huv
  have hc := (clique_ncard_le_cliqueNum hbig).trans hclique
  rw [Set.ncard_insert_of_notMem hxB, hc1] at hc
  omega

theorem outsideBall_independent_triple {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X R : Set V} {x : V} {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (htk : t < k)
    (hR : R ⊆ X) (hx : x ∈ R) (hcardR : R.ncard = t) (hX : X.ncard ≤ k)
    (hclique : G.cliqueNum ≤ t) (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (hexp : ∀ I : Set V, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard)
    (hmiss : ∀ u ∈ outsideBall G X x 1, ∀ z ∈ R \ {x}, ¬ G.Adj u z)
    (hnclique : ¬ G.IsClique (outsideBall G X x 1)) :
    3 ≤ independence G (outsideBall G X x 2) := by
  have ha : 2 ≤ independence G (outsideBall G X x 1) := by
    by_contra hn
    exact hnclique (clique_of_independence_le_one (by omega))
  obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G X x 1)
  have hIn : I.Nonempty := (Set.ncard_pos).mp (by omega)
  have he := hexp I hI hIn
  have hb := outside_neighborhood_bound hIs (Set.sdiff_subset.trans hR)
    (fun u hu => hmiss u (hIs hu))
  have hcZ : (R \ {x}).ncard = t - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hx, hcardR]
  rw [hcZ] at hb
  change (closedNeighborhood G I).ncard + (t - 1) ≤ X.ncard + (outsideBall G X x 2).ncard at hb
  have hm : 2 * k ≤ k * I.ncard := by
    have hh := Nat.mul_le_mul_left k (show 2 ≤ I.ncard by omega)
    simpa only [Nat.mul_comm k 2] using hh
  apply size_test hk ht hcycle hclique
  omega

theorem outsideBall_misses_representatives {V : Type*} {G : SimpleGraph V}
    {X R : Set V} {x : V} {r : ℕ} (hR : R ⊆ X) (hx : x ∈ R)
    (hno : ∀ y ∈ R, ∀ d, 1 ≤ d → d ≤ r + 1 → ¬ OutsidePath G X x y d) :
    ∀ u ∈ outsideBall G X x r, ∀ z ∈ R \ {x}, ¬ G.Adj u z := by
  intro u hu z hz
  exact outside_ball_misses (hR hx) (hR hz.1) (Ne.symm hz.2)
    (fun d hd hd' => hno z hz.1 d hd hd') u hu

end CycleClique

end OAI
