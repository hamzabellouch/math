import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RootedTemplates

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def reindexSet {N : ℕ} (s e : Finset (Fin N)) : Finset (Fin s.card) :=
  Finset.univ.filter (fun i => s.orderEmbOfFin rfl i ∈ e)

@[simp] lemma mem_reindexSet {N : ℕ} (s e : Finset (Fin N)) (i : Fin s.card) :
    i ∈ reindexSet s e ↔ s.orderEmbOfFin rfl i ∈ e := by
  simp only [reindexSet,Finset.mem_filter,Finset.mem_univ,true_and]

lemma image_reindexSet {N : ℕ} {s e : Finset (Fin N)} (he : e ⊆ s) :
    (reindexSet s e).image (s.orderEmbOfFin rfl) = e := by
  ext x
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact (mem_reindexSet s e i).mp hi
  · intro hx
    let i := (s.orderIsoOfFin rfl).symm ⟨x,he hx⟩
    have hi : s.orderEmbOfFin rfl i = x :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,he hx⟩)
    exact Finset.mem_image.mpr ⟨i,(mem_reindexSet s e i).mpr (by rwa [hi]),hi⟩

lemma reindexSet_card {N : ℕ} {s e : Finset (Fin N)} (he : e ⊆ s) :
    (reindexSet s e).card = e.card := by
  have hc := Finset.card_image_of_injective (reindexSet s e) (s.orderEmbOfFin rfl).injective
  rw [image_reindexSet he] at hc
  exact hc.symm

lemma reindexSet_inj {N : ℕ} {s e f : Finset (Fin N)} (he : e ⊆ s) (hf : f ⊆ s)
    (h : reindexSet s e = reindexSet s f) : e = f := by
  rw [← image_reindexSet he,← image_reindexSet hf,h]

lemma reindexSet_subset_iff {N : ℕ} {s e f : Finset (Fin N)} (he : e ⊆ s) :
    reindexSet s e ⊆ reindexSet s f ↔ e ⊆ f := by
  constructor
  · intro h x hx
    rw [← image_reindexSet he] at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_reindexSet s f i).mp (h hi)
  · intro h i hi
    exact (mem_reindexSet s f i).mpr (h ((mem_reindexSet s e i).mp hi))

lemma reindexSet_union {N : ℕ} (s e f : Finset (Fin N)) :
    reindexSet s (e ∪ f) = reindexSet s e ∪ reindexSet s f := by
  ext i
  simp only [mem_reindexSet,Finset.mem_union]

def reindexTemplate {N : ℕ} (s : Finset (Fin N)) (E : Graph N) (I : Finset (Fin N))
    (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) : RootedTemplate s.card where
  edges := E.image (reindexSet s)
  roots := reindexSet s I
  simple := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    rw [reindexSet_card (hE f hf),hsimple f hf]
  independent := by
    intro e he hs
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact hind f hf ((reindexSet_subset_iff (hE f hf)).mp hs)

lemma reindexTemplate_edges_card {N : ℕ} (s : Finset (Fin N)) (E : Graph N)
    (I : Finset (Fin N)) (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) :
    (reindexTemplate s E I hE hsimple hind).edges.card = E.card := by
  exact Finset.card_image_of_injOn (fun e he f hf h => reindexSet_inj (hE e he) (hE f hf) h)

lemma reindexTemplate_roots_card {N : ℕ} (s : Finset (Fin N)) (E : Graph N)
    (I : Finset (Fin N)) (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hI : I ⊆ s) :
    (reindexTemplate s E I hE hsimple hind).roots.card = I.card := reindexSet_card hI

lemma reindexTemplate_induced_card {N : ℕ} (s : Finset (Fin N)) (E : Graph N)
    (I : Finset (Fin N)) (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (U : Finset (Fin N)) :
    (((reindexTemplate s E I hE hsimple hind).edges).filter
      (fun e => e ⊆ reindexSet s U)).card = (E.filter (fun e => e ⊆ U)).card := by
  have heq : ((E.image (reindexSet s)).filter (fun e => e ⊆ reindexSet s U)) =
      (E.filter (fun e => e ⊆ U)).image (reindexSet s) := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hs⟩
      exact ⟨f,⟨hf,(reindexSet_subset_iff (hE f hf)).mp hs⟩,rfl⟩
    · rintro ⟨f,⟨hf,hs⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,(reindexSet_subset_iff (hE f hf)).mpr hs⟩
  change ((E.image (reindexSet s)).filter _).card = _
  rw [heq]
  exact Finset.card_image_of_injOn (fun e he f hf h =>
    reindexSet_inj (hE e (Finset.mem_filter.mp he).1) (hE f (Finset.mem_filter.mp hf).1) h)

end SharpTerminalLeave

end

end OAI
