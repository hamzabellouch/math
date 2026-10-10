import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalCrossing

namespace OAI

/-! A crossing layer preserves unordered edge support under relabeling of
the old vertices and crossing cells. Couplings do not enter this statement. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalCrossingLayer
open MediatorGraph
open scoped Classical

variable {r s : ℕ} (C : QMARationalCrossingLayer r) (E : QMARationalCrossingLayer s)
    (vertex : Fin C.base.n ≃ Fin E.base.n) (cell : Fin r ≃ Fin s)

def vertexRelabel : Fin (C.base.n+r*2) ≃ Fin (E.base.n+s*2) :=
  ((vertexEquiv C.base.n r).symm.trans
    (Equiv.sumCongr vertex (Equiv.prodCongr cell (Equiv.refl (Fin 2))))).trans
      (vertexEquiv E.base.n s)

theorem vertexRelabel_old (v : Fin C.base.n) :
    C.vertexRelabel E vertex cell (old C.base.n r v) = old E.base.n s (vertex v) := by
  simp [vertexRelabel,old]

theorem vertexRelabel_fresh (i : Fin r) (a : Fin 2) :
    C.vertexRelabel E vertex cell (fresh C.base.n r i a) =
      fresh E.base.n s (cell i) a := by
  simp [vertexRelabel,fresh]

variable
    (site : ∀ i a, vertex (C.site i a) = E.site (cell i) a)
    (forward : ∀ e : C.base.Edge, ∃ f : E.base.Edge,
      s(vertex (C.base.left e),vertex (C.base.right e)) = s(E.base.left f,E.base.right f))
    (backward : ∀ f : E.base.Edge, ∃ e : C.base.Edge,
      s(vertex (C.base.left e),vertex (C.base.right e)) = s(E.base.left f,E.base.right f))

include site forward in
theorem output_edge_source (N M : ℚ) (e : (C.output N).Edge) :
    ∃ f : (E.output M).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f) := by
  rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
  · obtain ⟨f,hf⟩ := forward e
    refine ⟨.inl (.inl f),?_⟩
    simpa only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inl,vertexRelabel_old,
      Sym2.map_mk] using congrArg (Sym2.map (old E.base.n s)) hf
  · refine ⟨.inl (.inr (cell i,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inr,vertexRelabel_old,site]
  · refine ⟨.inr (.inl (cell i)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,vertexRelabel_fresh]
  · refine ⟨.inr (.inr (cell i,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      vertexRelabel_old,vertexRelabel_fresh,site]

include site backward in
theorem output_edge_target (N M : ℚ) (f : (E.output M).Edge) :
    ∃ e : (C.output N).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f) := by
  rcases f with (f | ⟨j,a⟩) | (j | ⟨j,a⟩)
  · obtain ⟨e,he⟩ := backward f
    refine ⟨.inl (.inl e),?_⟩
    simpa only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inl,vertexRelabel_old,
      Sym2.map_mk] using congrArg (Sym2.map (old E.base.n s)) he
  · refine ⟨.inl (.inr (cell.symm j,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      qmaCrossingsBaseLeft,qmaCrossingsBaseRight,Sum.elim_inr,vertexRelabel_old,site,
      Equiv.apply_symm_apply]
  · refine ⟨.inr (.inl (cell.symm j)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,vertexRelabel_fresh,
      Equiv.apply_symm_apply]
  · refine ⟨.inr (.inr (cell.symm j,a)),?_⟩
    simp only [output,qmaParallelGraphLeft,qmaParallelGraphRight,
      vertexRelabel_old,vertexRelabel_fresh,site,Equiv.apply_symm_apply]

include site forward backward in
theorem output_support (N M : ℚ) :
    (∀ e : (C.output N).Edge, ∃ f : (E.output M).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) ∧
    (∀ f : (E.output M).Edge, ∃ e : (C.output N).Edge,
      s(C.vertexRelabel E vertex cell ((C.output N).left e),
        C.vertexRelabel E vertex cell ((C.output N).right e)) =
          s((E.output M).left f,(E.output M).right f)) :=
  ⟨C.output_edge_source E vertex cell site forward N M,
    C.output_edge_target E vertex cell site backward N M⟩

end ContinuumCoulomb.QMARationalCrossingLayer

end

end OAI
