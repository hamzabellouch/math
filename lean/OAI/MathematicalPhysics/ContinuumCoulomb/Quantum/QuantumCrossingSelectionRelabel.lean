import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectionUnique

namespace OAI

/-! A relabeling of the old graph and the crossing cells preserves exactly
which edges are retained by the physical crossing selection. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalExchangeGraph
open scoped Classical

variable {G H : QMARationalExchangeGraph} {r t : ℕ}
    (vertex : Fin G.n ≃ Fin H.n) (edge : G.Edge ≃ H.Edge)
    (left : ∀ e, vertex (G.left e)=H.left (edge e))
    (right : ∀ e, vertex (G.right e)=H.right (edge e))
    (s : Fin r → Fin 4 → Fin G.n) (u : Fin t → Fin 4 → Fin H.n)
    (cell : Fin r ≃ Fin t) (site : ∀ i a, vertex (s i a)=u (cell i) a)

include left right site in
theorem crossingMatch_relabel (e : G.Edge) (i : Fin r) (a : Fin 2) :
    G.CrossingMatch s e (i,a) ↔ H.CrossingMatch u (edge e) (cell i,a) := by
  have hl (b : Fin 4) : G.left e=s i b ↔ H.left (edge e)=u (cell i) b := by
    rw [← left e,← site i b]
    exact vertex.injective.eq_iff.symm
  have hr (b : Fin 4) : G.right e=s i b ↔ H.right (edge e)=u (cell i) b := by
    rw [← right e,← site i b]
    exact vertex.injective.eq_iff.symm
  simp only [CrossingMatch,hl,hr]

include left right site in
theorem crossingTag_none_relabel (e : G.Edge) :
    G.crossingTag s e=none ↔ H.crossingTag u (edge e)=none := by
  rw [G.crossingTag_none,H.crossingTag_none]
  constructor
  · intro h ⟨i,a⟩ hp
    apply h (cell.symm i,a)
    apply (crossingMatch_relabel vertex edge left right s u cell site e _ a).mpr
    simpa only [Equiv.apply_symm_apply] using hp
  · intro h ⟨i,a⟩ hp
    exact h (cell i,a) ((crossingMatch_relabel vertex edge left right s u cell site e i a).mp hp)

variable (hs : ∀ i, Function.Injective (s i)) (hu : ∀ i, Function.Injective (u i))

include left right site in
theorem retained_source (e : (G.crossingSelection s hs).retained.Edge) :
    ∃ f : (H.crossingSelection u hu).retained.Edge,
      vertex (G.left e.val)=H.left f.val ∧ vertex (G.right e.val)=H.right f.val := by
  refine ⟨⟨edge e.val,(crossingTag_none_relabel vertex edge left right s u cell site e.val).mp
    e.property⟩,left e.val,right e.val⟩

include left right site in
theorem retained_target (f : (H.crossingSelection u hu).retained.Edge) :
    ∃ e : (G.crossingSelection s hs).retained.Edge,
      vertex (G.left e.val)=H.left f.val ∧ vertex (G.right e.val)=H.right f.val := by
  have ht : G.crossingTag s (edge.symm f.val)=none :=
    (crossingTag_none_relabel vertex edge left right s u cell site (edge.symm f.val)).mpr
      (by rw [Equiv.apply_symm_apply]; exact f.property)
  refine ⟨⟨edge.symm f.val,ht⟩,?_,?_⟩
  · simpa only [Equiv.apply_symm_apply] using left (edge.symm f.val)
  · simpa only [Equiv.apply_symm_apply] using right (edge.symm f.val)

end ContinuumCoulomb.QMARationalExchangeGraph

end

end OAI
