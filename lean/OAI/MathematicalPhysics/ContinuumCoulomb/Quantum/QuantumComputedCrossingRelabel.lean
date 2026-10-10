import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectionRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSupportRelabel

namespace OAI

/-! The computed retained-edge scan and the canonical crossing layer have
the same physical edges after the old spins and crossing cells are relabeled. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open scoped Classical

variable {G H : QMARationalExchangeGraph} {r t m : ℕ}
    (vertex : Fin G.n ≃ Fin H.n) (edge : G.Edge ≃ H.Edge)
    (left : ∀ e, vertex (G.left e)=H.left (edge e))
    (right : ∀ e, vertex (G.right e)=H.right (edge e))
    (s : Fin r → Fin 4 → Fin G.n) (u : Fin t → Fin 4 → Fin H.n)
    (cell : Fin r ≃ Fin t) (site : ∀ i a, vertex (s i a)=u (cell i) a)
    (hs : ∀ i, Function.Injective (s i)) (hu : ∀ i, Function.Injective (u i))
    (hglobal : Function.Injective (fun p : Fin r × Fin 4 => s p.1 p.2))
    (labels : G.Edge ≃ Fin m)

include left right site hglobal in
theorem computed_base_source
    (e : (computedLayer (G.crossingSelection s hs) labels).base.Edge) :
    ∃ f : (H.crossingSelection u hu).layer.base.Edge,
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.left e) =
        (H.crossingSelection u hu).layer.base.left f ∧
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.right e) =
        (H.crossingSelection u hu).layer.base.right f := by
  have ht := fun e i a => G.crossingTag_some_iff s hglobal e (i,a)
  obtain ⟨k,hk1,hk2⟩ := retained_edge_source (G.crossingSelection s hs) labels ht e
  obtain ⟨f,hf1,hf2⟩ := QMARationalExchangeGraph.retained_source vertex edge left right s u cell site hs hu k
  exact ⟨f,(congrArg vertex hk1).trans hf1,(congrArg vertex hk2).trans hf2⟩

include left right site hglobal in
theorem computed_base_target (f : (H.crossingSelection u hu).layer.base.Edge) :
    ∃ e : (computedLayer (G.crossingSelection s hs) labels).base.Edge,
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.left e) =
        (H.crossingSelection u hu).layer.base.left f ∧
      vertex ((computedLayer (G.crossingSelection s hs) labels).base.right e) =
        (H.crossingSelection u hu).layer.base.right f := by
  have ht := fun e i a => G.crossingTag_some_iff s hglobal e (i,a)
  obtain ⟨k,hk1,hk2⟩ := QMARationalExchangeGraph.retained_target vertex edge left right s u cell site hs hu f
  obtain ⟨e,he1,he2⟩ := retained_edge_target (G.crossingSelection s hs) labels ht k
  exact ⟨e,(congrArg vertex he1).trans hk1,(congrArg vertex he2).trans hk2⟩

include left right site hglobal in
theorem computed_output_support (N M : ℚ) :
    let C := computedLayer (G.crossingSelection s hs) labels
    let E := (H.crossingSelection u hu).layer
    (∀ e : (C.output N).Edge, ∃ f : (E.output M).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) ∧
    (∀ f : (E.output M).Edge, ∃ e : (C.output N).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) := by
  let C := computedLayer (G.crossingSelection s hs) labels
  let E := (H.crossingSelection u hu).layer
  apply C.output_support E vertex cell site
  · intro e
    obtain ⟨f,h1,h2⟩ := computed_base_source vertex edge left right s u cell site hs hu hglobal labels e
    exact ⟨f,congrArg₂ (fun a b : Fin H.n => s(a,b)) h1 h2⟩
  · intro f
    obtain ⟨e,h1,h2⟩ := computed_base_target vertex edge left right s u cell site hs hu hglobal labels f
    exact ⟨e,congrArg₂ (fun a b : Fin H.n => s(a,b)) h1 h2⟩

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
