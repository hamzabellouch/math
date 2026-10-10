import OAI.Combinatorics.BalancedRyser.Construction.PartitionEncoding
import OAI.Combinatorics.BalancedRyser.Hypergraph

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {G X : Type*} [Fintype X] {Label : G → Type*} {r n : ℕ}

def partitionHypergraph (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) : PartiteHypergraph r n where
  edges := Finset.univ.image (encodeAssignment eG eL label)

@[simp] theorem mem_partitionHypergraph_edges
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (e : Fin r → Fin n) :
    e ∈ (partitionHypergraph eG eL label).edges ↔
      ∃ x, encodeAssignment eG eL label x = e := by
  classical
  simp [partitionHypergraph]

theorem partitionHypergraph_nonisolated
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hblocks : ∀ g, Function.Surjective (label g)) :
    (partitionHypergraph eG eL label).Nonisolated := by
  intro i v
  obtain ⟨x, hx⟩ := hblocks (eG.symm i) ((eL (eG.symm i)).symm v)
  refine ⟨encodeAssignment eG eL label x, ?_, ?_⟩
  · exact (mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩
  · simp [encodeAssignment, hx]

theorem partitionHypergraph_intersecting [Nonempty X]
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hagrees : ∀ x y, ∃ g, label g x = label g y) :
    (partitionHypergraph eG eL label).Intersecting := by
  constructor
  · obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨_, (mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩⟩
  · intro e he f hf
    obtain ⟨x, rfl⟩ := (mem_partitionHypergraph_edges eG eL label e).mp he
    obtain ⟨y, rfl⟩ := (mem_partitionHypergraph_edges eG eL label f).mp hf
    exact (encodeAssignment_agree_iff eG eL label x y).mpr (hagrees x y)

noncomputable def partitionHypergraph_edgeEquiv
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hinj : Function.Injective (fun x g => label g x)) :
    X ≃ {e // e ∈ (partitionHypergraph eG eL label).edges} :=
  Equiv.ofBijective
    (fun x => ⟨encodeAssignment eG eL label x,
      (mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩⟩)
    (by
      constructor
      · intro x y hxy
        exact encodeAssignment_injective eG eL label hinj (congrArg Subtype.val hxy)
      · intro e
        obtain ⟨x, hx⟩ := (mem_partitionHypergraph_edges eG eL label e.val).mp e.property
        exact ⟨x, Subtype.ext hx⟩)

theorem partitionHypergraph_covers_iff
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (C : Finset (Fin r × Fin n)) :
    (partitionHypergraph eG eL label).Covers C ↔
      ∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈
        C.map (encodeLabel eG eL).symm.toEmbedding := by
  constructor
  · intro h x
    apply (encodeAssignment_covered_iff eG eL label x C).mp
    exact h _ ((mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩)
  · intro h e he
    obtain ⟨x, rfl⟩ := (mem_partitionHypergraph_edges eG eL label e).mp he
    exact (encodeAssignment_covered_iff eG eL label x C).mpr (h x)

theorem partitionHypergraph_cover_lower_bound
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (k : ℕ)
    (hblocks : ∀ C : Finset (Sigma Label),
      (∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈ C) → k ≤ C.card) :
    ∀ C, (partitionHypergraph eG eL label).Covers C → k ≤ C.card := by
  intro C hC
  have h := hblocks (C.map (encodeLabel eG eL).symm.toEmbedding)
    ((partitionHypergraph_covers_iff eG eL label C).mp hC)
  simpa using h

theorem partitionHypergraph_hasCoverNumber [Nonempty G]
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hblocks : ∀ C : Finset (Sigma Label),
      (∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈ C) → n ≤ C.card) :
    (partitionHypergraph eG eL label).HasCoverNumber n := by
  classical
  constructor
  · obtain ⟨g⟩ := ‹Nonempty G›
    refine ⟨Finset.univ.image (fun v : Fin n => (eG g, v)), ?_, ?_⟩
    · intro e he
      exact ⟨eG g, Finset.mem_image.mpr ⟨e (eG g), Finset.mem_univ _, rfl⟩⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
      exact Finset.card_fin n
  · exact partitionHypergraph_cover_lower_bound eG eL label n hblocks

theorem exists_partiteHypergraph_of_partitions [Nonempty X] [Nonempty G]
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hne : ∀ g, Function.Surjective (label g))
    (hinter : ∀ x y, ∃ g, label g x = label g y)
    (hinj : Function.Injective (fun x g => label g x))
    (hcover : ∀ C : Finset (Sigma Label),
      (∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈ C) → n ≤ C.card) :
    ∃ H : PartiteHypergraph r n,
      H.Intersecting ∧ H.Nonisolated ∧ H.HasCoverNumber n ∧
        Nonempty (X ≃ {e // e ∈ H.edges}) := by
  refine ⟨partitionHypergraph eG eL label,
    partitionHypergraph_intersecting eG eL label hinter,
    partitionHypergraph_nonisolated eG eL label hne,
    partitionHypergraph_hasCoverNumber eG eL label hcover, ?_⟩
  exact ⟨partitionHypergraph_edgeEquiv eG eL label hinj⟩

end Balanced

end OAI
