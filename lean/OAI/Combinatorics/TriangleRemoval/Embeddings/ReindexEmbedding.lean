import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ReindexSet

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def reindexEmbedding {N n : ℕ} (s : Finset (Fin N)) (φ : Fin N ↪ Fin n) :
    Fin s.card ↪ Fin n := (s.orderEmbOfFin rfl).toEmbedding.trans φ

@[simp] lemma reindexEmbedding_apply {N n : ℕ} (s : Finset (Fin N))
    (φ : Fin N ↪ Fin n) (i : Fin s.card) :
    reindexEmbedding s φ i = φ (s.orderEmbOfFin rfl i) := rfl

lemma reindexEdges_map {N n : ℕ} {s e : Finset (Fin N)} (he : e ⊆ s)
    (φ : Fin N ↪ Fin n) :
    (reindexSet s e).map (reindexEmbedding s φ) = e.map φ := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨s.orderEmbOfFin rfl i,(mem_reindexSet s e i).mp hi,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    rw [← image_reindexSet he] at hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i,hi,rfl⟩

def boundaryInjection {N n : ℕ} (s I P : Finset (Fin N)) (hIP : I ⊆ P)
    (ξ : {x // x ∈ P} ↪ Fin n) : {i // i ∈ reindexSet s I} ↪ Fin n where
  toFun i := ξ ⟨s.orderEmbOfFin rfl i, hIP ((mem_reindexSet s I i).mp i.property)⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact (s.orderEmbOfFin rfl).injective
      (congrArg (fun x : {x // x ∈ P} => x.val) (ξ.injective hij))

theorem graphEmbedding_fiber_le_rootedCount {N n : ℕ}
    (s I P : Finset (Fin N)) (E F : Graph N) (G : Graph n)
    (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hIP : I ⊆ P)
    (hcover : P ∪ s = Finset.univ) (hEF : E ⊆ F)
    (ξ : {x // x ∈ P} ↪ Fin n) :
    (((Finset.univ.filter (fun φ : Fin N ↪ Fin n =>
      (∀ x : {x // x ∈ P}, φ x = ξ x) ∧ F.image (fun e => e.map φ) ⊆ G)).card : ℕ) : ℝ) ≤
      rootedCount (reindexTemplate s E I hE hsimple hind)
        (boundaryInjection s I P hIP ξ) G := by
  classical
  let T := reindexTemplate s E I hE hsimple hind
  let ψ := boundaryInjection s I P hIP ξ
  let A := Finset.univ.filter (fun φ : Fin N ↪ Fin n =>
    (∀ x : {x // x ∈ P}, φ x = ξ x) ∧ F.image (fun e => e.map φ) ⊆ G)
  let B := Finset.univ.filter (fun φ : RootedInjection T ψ => imageEdges T φ.val ⊆ G)
  have hf (φ : Fin N ↪ Fin n) (hφ : φ ∈ A) :
      ∀ i : {i // i ∈ T.roots}, reindexEmbedding s φ i = ψ i := by
    intro i
    exact (Finset.mem_filter.mp hφ).2.1
      ⟨s.orderEmbOfFin rfl i,hIP ((mem_reindexSet s I i).mp i.property)⟩
  let f (φ : {φ // φ ∈ A}) : RootedInjection T ψ :=
    ⟨reindexEmbedding s φ.val,hf φ.val φ.property⟩
  have hfmem (φ : {φ // φ ∈ A}) : f φ ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro e he
    obtain ⟨es,hes,rfl⟩ := Finset.mem_image.mp he
    change es ∈ E.image (reindexSet s) at hes
    obtain ⟨ef,hef,rfl⟩ := Finset.mem_image.mp hes
    change (reindexSet s ef).map (reindexEmbedding s φ.val) ∈ G
    rw [reindexEdges_map (hE ef hef)]
    exact (Finset.mem_filter.mp φ.property).2.2
      (Finset.mem_image.mpr ⟨ef,hEF hef,rfl⟩)
  have hfinj : Function.Injective f := by
    intro φ χ heq
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    have hx : x ∈ P ∪ s := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hx with hxP | hxs
    · exact ((Finset.mem_filter.mp φ.property).2.1 ⟨x,hxP⟩).trans
        ((Finset.mem_filter.mp χ.property).2.1 ⟨x,hxP⟩).symm
    · obtain ⟨i,hi⟩ := (s.orderIsoOfFin rfl).surjective ⟨x,hxs⟩
      have hix : s.orderEmbOfFin rfl i = x := congrArg Subtype.val hi
      have hh := congrArg (fun y : RootedInjection T ψ => y.val i) heq
      change φ.val (s.orderEmbOfFin rfl i) = χ.val (s.orderEmbOfFin rfl i) at hh
      rwa [hix] at hh
  have hcard : A.card ≤ B.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      (fun φ : {φ // φ ∈ A} => (⟨f φ,hfmem φ⟩ : {χ // χ ∈ B}))
      (fun φ χ h => hfinj (congrArg Subtype.val h))
  have hcount : rootedCount T ψ G = (B.card : ℝ) := by
    simp [rootedCount,copyCount,intact,B]
  change (A.card : ℝ) ≤ rootedCount T ψ G
  rw [hcount]
  exact_mod_cast hcard

end SharpTerminalLeave

end

end OAI
