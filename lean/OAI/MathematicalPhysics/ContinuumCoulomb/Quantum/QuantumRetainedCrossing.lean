import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPairSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortCrossingSelection
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortLinks

namespace OAI

/-! Every edge internal to a selected crossing is removed from the retained
graph. The assertion concerns the actual completed subdivision graph. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCrossPair_direction (a b : Fin 4) (h : s(a,b) ∈ qmaCrossPortPairing) :
    ∃ t : Fin 2,
      (a = qmaPatchDirection (if t = 0 then 0 else 1) ∧
       b = qmaPatchDirection (if t = 0 then 2 else 3)) ∨
      (a = qmaPatchDirection (if t = 0 then 2 else 3) ∧
       b = qmaPatchDirection (if t = 0 then 0 else 1)) := by
  have hfinite : ∀ a b : Fin 4, s(a,b) ∈ qmaCrossPortPairing →
      ∃ t : Fin 2,
        (a = qmaPatchDirection (if t = 0 then 0 else 1) ∧
         b = qmaPatchDirection (if t = 0 then 2 else 3)) ∨
        (a = qmaPatchDirection (if t = 0 then 2 else 3) ∧
         b = qmaPatchDirection (if t = 0 then 0 else 1)) := by decide
  exact hfinite a b h

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem finished_edge_adjacent (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.finishedGraph N D).Edge) :
    P.graph.Adj (P.finishedPosition N D ((P.finishedGraph N D).left e))
      (P.finishedPosition N D ((P.finishedGraph N D).right e)) :=
  (P.toEmbedding.iterate N D).adjacent_of_complete (P.schedule.iterate_complete N hD) e

theorem graph_link {x y : ℕ × ℕ} (h : P.graph.Adj x y) : QMAPortLink x y := by
  change _ ≠ _ ∧ _ at h
  rcases h.2 with ⟨e,k,hk,hl,hr⟩ | ⟨e,k,hk,hl,hr⟩
  · rw [← hl,← hr]
    exact qmaPortChain_link (P.point e) (P.length_pos e) (P.step e) k hk
  · rw [← hl,← hr]
    exact (qmaPortChain_link (P.point e) (P.length_pos e) (P.step e) k hk).symm

theorem finished_edge_link (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.finishedGraph N D).Edge) :
    QMAPortLink (P.finishedPosition N D ((P.finishedGraph N D).left e))
      (P.finishedPosition N D ((P.finishedGraph N D).right e)) :=
  P.graph_link (P.finished_edge_adjacent N hD e)

theorem retained_no_internal_crossing (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (e : (P.portCrossingSelection N hD).retained.Edge) (c : P.Crossing) (a b : Fin 4)
    (hl : P.finishedPosition N D ((P.finishedGraph N D).left e.val) = qmaGridPort c.val a)
    (hr : P.finishedPosition N D ((P.finishedGraph N D).right e.val) = qmaGridPort c.val b) : False := by
  have ha := P.finished_edge_adjacent N hD e.val
  rw [hl,hr] at ha
  obtain ⟨t,hab⟩ := qmaCrossPair_direction a b
    (P.crossing_graph_pair (P.mem_crossingCells.mp c.property) ha)
  let i : Fin P.crossingCells.card := P.crossingCells.equivFin c
  have hi : P.crossingCell i = c := P.crossingCells.equivFin.symm_apply_apply c
  have hsite (u : Fin 4) : P.finishedPosition N D (P.crossingSiteFin N hD i u) =
      qmaGridPort c.val (qmaPatchDirection u) := by
    change P.finishedPosition N D (P.crossingSite N hD (P.crossingCell i) _) = _
    rw [hi,P.crossingSite_spec]
  have hinj := (P.toEmbedding.iterate N D).position_injective
  have hvertex (v : Fin (P.finishedGraph N D).n) (u : Fin 4)
      (hv : P.finishedPosition N D v = qmaGridPort c.val (qmaPatchDirection u)) :
      v = P.crossingSiteFin N hD i u := hinj (hv.trans (hsite u).symm)
  apply (P.finishedGraph N D).retained_no_crossing (P.crossingSiteFin N hD)
    (P.crossingSiteFin_injective N hD) e (i,t)
  rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨hvertex _ _ (by simpa only [ha] using hl),
      hvertex _ _ (by simpa only [hb] using hr)⟩
  · exact Or.inr ⟨hvertex _ _ (by simpa only [ha] using hl),
      hvertex _ _ (by simpa only [hb] using hr)⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
