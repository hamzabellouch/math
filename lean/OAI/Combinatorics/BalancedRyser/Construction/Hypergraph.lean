import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Hypergraph

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

@[simp] theorem mem_part (i j : Fin r) (v : Fin n) :
    (j, v) ∈ part (n := n) i ↔ j = i := by
  simp [part, Prod.mk.injEq, eq_comm]

@[simp] theorem mem_edgeVertices (e : Fin r → Fin n) (i : Fin r) (v : Fin n) :
    (i, v) ∈ edgeVertices e ↔ e i = v := by
  simp [edgeVertices, Prod.mk.injEq, eq_comm]

@[simp] theorem card_part (i : Fin r) : (part (n := n) i).card = n := by
  rw [part, Finset.card_image_of_injective]
  · simp
  · intro v w h
    exact (Prod.mk.inj h).2

@[simp] theorem card_edgeVertices (e : Fin r → Fin n) :
    (edgeVertices e).card = r := by
  rw [edgeVertices, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact (Prod.mk.inj h).1

theorem disjoint_parts {i j : Fin r} (hij : i ≠ j) :
    Disjoint (part (n := n) i) (part (n := n) j) := by
  rw [Finset.disjoint_left]
  rintro ⟨k, v⟩ hi hj
  simp only [mem_part] at hi hj
  exact hij (hi.symm.trans hj)

theorem edgeVertices_inter_part (e : Fin r → Fin n) (i : Fin r) :
    edgeVertices e ∩ part i = {(i, e i)} := by
  ext x
  rcases x with ⟨j, v⟩
  simp only [Finset.mem_inter, mem_edgeVertices, mem_part, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨he, rfl⟩
    exact ⟨rfl, he.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem edgeVertices_injective :
    Function.Injective (edgeVertices (r := r) (n := n)) := by
  intro e f h
  funext i
  have hi : (i, e i) ∈ edgeVertices f := by
    rw [← h]
    simp
  exact (mem_edgeVertices f i (e i)).mp hi |>.symm

theorem edgeVertices_inter_nonempty_iff (e f : Fin r → Fin n) :
    (edgeVertices e ∩ edgeVertices f).Nonempty ↔ ∃ i, e i = f i := by
  constructor
  · rintro ⟨⟨i, v⟩, h⟩
    rcases Finset.mem_inter.mp h with ⟨he, hf⟩
    exact ⟨i, (mem_edgeVertices e i v).mp he |>.trans
      ((mem_edgeVertices f i v).mp hf).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨(i, e i), by simp [hi]⟩

theorem covers_iff_inter_nonempty (H : PartiteHypergraph r n)
    (C : Finset (Vertex r n)) :
    H.Covers C ↔ ∀ e ∈ H.edges, (C ∩ edgeVertices e).Nonempty := by
  constructor
  · intro h e he
    rcases h e he with ⟨i, hi⟩
    exact ⟨(i, e i), by simp [hi]⟩
  · intro h e he
    rcases h e he with ⟨⟨i, v⟩, hv⟩
    rcases Finset.mem_inter.mp hv with ⟨hc, hv⟩
    have hev := (mem_edgeVertices e i v).mp hv
    exact ⟨i, by simpa [hev] using hc⟩

theorem part_covers (H : PartiteHypergraph r n) (i : Fin r) :
    H.Covers (part i) := by
  intro e he
  exact ⟨i, by simp⟩

theorem exists_cover_card (H : PartiteHypergraph r n) (hr : 0 < r) :
    ∃ C : Finset (Vertex r n), H.Covers C ∧ C.card = n := by
  exact ⟨part ⟨0, hr⟩, H.part_covers _, card_part _⟩

theorem hasCoverNumber_iff (H : PartiteHypergraph r n) (hr : 0 < r) :
    H.HasCoverNumber n ↔ ∀ C, H.Covers C → n ≤ C.card := by
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨H.exists_cover_card hr, h⟩

theorem hasCoverNumber_unique (H : PartiteHypergraph r n) {k l : ℕ}
    (hk : H.HasCoverNumber k) (hl : H.HasCoverNumber l) : k = l := by
  rcases hk.1 with ⟨C, hC, hcardC⟩
  rcases hl.1 with ⟨D, hD, hcardD⟩
  have hkl := hk.2 D hD
  have hlk := hl.2 C hC
  omega

theorem coverNumber_le_part (H : PartiteHypergraph r n) (hr : 0 < r)
    {k : ℕ} (hk : H.HasCoverNumber k) : k ≤ n := by
  rcases H.exists_cover_card hr with ⟨C, hC, hcard⟩
  simpa [hcard] using hk.2 C hC

theorem covers_mono (H : PartiteHypergraph r n) {C D : Finset (Vertex r n)}
    (hC : H.Covers C) (hCD : C ⊆ D) : H.Covers D := by
  intro e he
  rcases hC e he with ⟨i, hi⟩
  exact ⟨i, hCD hi⟩

@[simp] theorem covers_empty_iff (H : PartiteHypergraph r n) :
    H.Covers ∅ ↔ H.edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases h e he with ⟨i, hi⟩
    exact Finset.notMem_empty _ hi
  · intro h e he
    simp [h] at he

theorem nonisolated_iff_mem_edge (H : PartiteHypergraph r n) :
    H.Nonisolated ↔ ∀ v : Vertex r n, ∃ e ∈ H.edges, v ∈ edgeVertices e := by
  constructor
  · intro h ⟨i, v⟩
    rcases h i v with ⟨e, he, hev⟩
    exact ⟨e, he, (mem_edgeVertices e i v).mpr hev⟩
  · intro h i v
    rcases h (i, v) with ⟨e, he, hev⟩
    exact ⟨e, he, (mem_edgeVertices e i v).mp hev⟩

theorem intersecting_iff (H : PartiteHypergraph r n) :
    H.Intersecting ↔ H.edges.Nonempty ∧
      ∀ e ∈ H.edges, ∀ f ∈ H.edges,
        (edgeVertices e ∩ edgeVertices f).Nonempty := by
  simp only [Intersecting, edgeVertices_inter_nonempty_iff]

theorem matching_card_le_one (H : PartiteHypergraph r n)
    (hH : H.Intersecting) {M : Finset (Fin r → Fin n)}
    (hM : H.IsMatching M) : M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  have hdisj := hM.2 e he f hf hne
  rcases hH.2 e (hM.1 he) f (hM.1 hf) with ⟨i, hi⟩
  exact Finset.disjoint_left.mp hdisj (by simp : (i, e i) ∈ edgeVertices e)
    (by simp [hi] : (i, e i) ∈ edgeVertices f)

theorem exists_matching_card_one (H : PartiteHypergraph r n)
    (hH : H.Intersecting) :
    ∃ M : Finset (Fin r → Fin n), H.IsMatching M ∧ M.card = 1 := by
  rcases hH.1 with ⟨e, he⟩
  refine ⟨{e}, ⟨?_, ?_⟩, by simp⟩
  · simpa using he
  · intro f hf g hg hne
    simp only [Finset.mem_singleton] at hf hg
    exact (hne (hf.trans hg.symm)).elim

theorem intersecting_iff_distinct (H : PartiteHypergraph r n) (hr : 0 < r) :
    H.Intersecting ↔ H.edges.Nonempty ∧
      ∀ e ∈ H.edges, ∀ f ∈ H.edges, e ≠ f → ∃ i, e i = f i := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun e he f hf _ => h e he f hf⟩
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    intro e he f hf
    by_cases hef : e = f
    · exact ⟨⟨0, hr⟩, by rw [hef]⟩
    · exact h e he f hf hef

theorem exists_hasCoverNumber (H : PartiteHypergraph r n) (hr : 0 < r) :
    ∃ k, H.HasCoverNumber k := by
  classical
  have hex : ∃ k, ∃ C : Finset (Vertex r n), H.Covers C ∧ C.card = k :=
    ⟨n, H.exists_cover_card hr⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro C hC
  exact Nat.find_min' hex ⟨C, hC, rfl⟩

theorem hasCoverNumber_succ_iff_no_small_cover {q : ℕ}
    (H : PartiteHypergraph r (q + 1)) (hr : 0 < r) :
    H.HasCoverNumber (q + 1) ↔
      ∀ C : Finset (Vertex r (q + 1)), C.card ≤ q → ¬H.Covers C := by
  rw [H.hasCoverNumber_iff hr]
  constructor
  · intro h C hsmall hC
    have := h C hC
    omega
  · intro h C hC
    by_contra hlarge
    exact h C (by omega) hC

end Balanced.PartiteHypergraph

end OAI
