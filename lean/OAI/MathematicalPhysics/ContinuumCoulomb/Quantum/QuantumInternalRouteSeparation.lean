import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedRoutes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellVisitPaths
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalPathClearance

namespace OAI

/-! Distinct permitted internal routes in a cell have disjoint interiors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev QMAInternalEdge := Fin 4 ⊕ (Fin 6 ⊕ Fin 9)

def qmaInternalPath : QMAInternalEdge → List (ℕ × ℕ)
  | .inl a => qmaCellRayPath a
  | .inr (.inl e) => qmaCellPairPath e
  | .inr (.inr e) => qmaLocalPatchPath e

def qmaInternalBody (p : ℕ × ℕ) : QMAInternalEdge → QMACellRouteBody
  | .inl a => .ray p a
  | .inr (.inl e) => .pair p e
  | .inr (.inr e) => .patch p e

theorem qmaCellPair_pair_injective : Function.Injective
    (fun e : Fin 6 => s(qmaCellPairLeft e,qmaCellPairRight e)) := by decide

theorem qmaInternalPath_bounded (e : QMAInternalEdge) :
    ∀ p ∈ qmaInternalPath e, p.1 < 32 ∧ p.2 < 32 := by
  rcases e with a | (e | e)
  · intro p hp
    obtain ⟨_,hx,_,hy⟩ := qmaCellRay_bounded a p hp
    omega
  · intro p hp
    obtain ⟨_,hx,_,hy⟩ := qmaCellPair_bounded e p hp
    omega
  · intro p hp
    obtain ⟨_,hx,_,hy⟩ := qmaLocalPatch_bounded e p hp
    omega

theorem qmaInternalBody_path (p : ℕ × ℕ) (e : QMAInternalEdge) :
    (qmaInternalBody p e).path = (qmaInternalPath e).map (qmaCellTranslate p) := by
  rcases e with a | (e | e)
  · rfl
  · rfl
  · change (qmaCrossingPatchPath e).map (qmaPatchTranslate p) =
      ((qmaCrossingPatchPath e).map (fun z => (10+z.1,10+z.2))).map (qmaCellTranslate p)
    rw [List.map_map]
    apply List.map_congr_left
    intro z _
    exact (qmaCellTranslate_patch p z).symm

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem routingPair_index {p : ℕ × ℕ} {e : Fin 6} (h : P.RoutingAllowed (.pair p e)) :
    ∃ i : P.Interior, P.cell i = p ∧ e = P.cellPairIndex i := by
  obtain ⟨_,i,hi,hp⟩ := h
  refine ⟨i,hi,qmaCellPair_pair_injective ?_⟩
  exact hp.symm.trans (P.cellPairIndex_pair i).symm

theorem internal_allowed_disjoint
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (p : ℕ × ℕ) (e f : QMAInternalEdge) (hef : e ≠ f)
    (he : P.RoutingAllowed (qmaInternalBody p e))
    (hf : P.RoutingAllowed (qmaInternalBody p f)) :
    Disjoint (((qmaInternalPath e).drop 1).dropLast).toFinset (qmaInternalPath f).toFinset := by
  rcases e with a | (a | a) <;> rcases f with b | (b | b)
  · change Disjoint (((qmaCellRayPath a).drop 1).dropLast).toFinset (qmaCellRayPath b).toFinset
    fin_cases a <;> fin_cases b <;> first | exact (hef rfl).elim | decide
  · obtain ⟨⟨v,hv⟩,_⟩ := he
    obtain ⟨_,i,hi,_⟩ := hf
    exact (havoid i v (hi.trans hv.symm)).elim
  · exact (he.2 hf).elim
  · obtain ⟨_,i,hi,_⟩ := he
    obtain ⟨⟨v,hv⟩,_⟩ := hf
    exact (havoid i v (hi.trans hv.symm)).elim
  · obtain ⟨i,hi,rfl⟩ := P.routingPair_index he
    obtain ⟨j,hj,rfl⟩ := P.routingPair_index hf
    have hij : i ≠ j := by
      intro h
      apply hef
      rw [h]
    have hn : ¬P.IsCrossing (P.cell i) := by simpa only [hi] using he.1
    have hd := P.ordinary_visit_paths_disjoint hij (hi.trans hj.symm) hn
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    apply Finset.disjoint_left.mp hd _ hz'
    exact List.mem_toFinset.mpr
      (List.mem_of_mem_drop (List.mem_of_mem_dropLast (List.mem_toFinset.mp hz)))
  · exact (he.1 hf).elim
  · exact (hf.2 he).elim
  · exact (hf.1 he).elim
  · change Disjoint (((qmaLocalPatchPath a).drop 1).dropLast).toFinset (qmaLocalPatchPath b).toFinset
    fin_cases a <;> fin_cases b <;> first | exact (hef rfl).elim | decide

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
