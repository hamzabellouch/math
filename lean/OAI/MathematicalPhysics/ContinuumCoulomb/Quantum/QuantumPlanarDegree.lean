import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelection

namespace OAI

/-! Disjoint lattice routes bound the actual edge-incidence degree by the four
available lattice directions, including edges whose orientation points inward. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMAPlanarRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)

abbrev Incident (_P : QMAPlanarRouteData G) (v : Fin G.n) := {e : G.Edge // G.left e = v ∨ G.right e = v}

def incidentNear (v : Fin G.n) (e : P.Incident v) : ℕ × ℕ :=
  if G.left e.val = v then P.point e.val 1 else P.point e.val (P.length e.val-1)

theorem incident_segment (v : Fin G.n) (e : P.Incident v) :
    ∃ k, k < P.length e.val ∧
      ((P.point e.val k = P.position v ∧ P.point e.val (k+1) = P.incidentNear v e) ∨
       (P.point e.val k = P.incidentNear v e ∧ P.point e.val (k+1) = P.position v)) := by
  by_cases h : G.left e.val = v
  · refine ⟨0,P.length_pos e.val,Or.inl ⟨?_,?_⟩⟩
    · rw [P.first,h]
    · simp only [incidentNear,h,ite_true]
  · have hr := e.property.resolve_left h
    have hpos := P.length_pos e.val
    have hlast : P.length e.val-1+1 = P.length e.val := by omega
    refine ⟨P.length e.val-1,by omega,Or.inr ⟨?_,?_⟩⟩
    · simp only [incidentNear,h,ite_false]
    · rw [hlast,P.last,hr]

theorem incident_position_positive (v : Fin G.n) (e : P.Incident v) :
    0 < (P.position v).1 ∧ 0 < (P.position v).2 := by
  rcases e.property with h | h
  · simpa only [P.first,h] using P.positive e.val 0 (Nat.zero_le _)
  · simpa only [P.last,h] using P.positive e.val (P.length e.val) le_rfl

theorem incident_adjacent (v : Fin G.n) (e : P.Incident v) :
    qmaSquareGrid.Adj (P.position v) (P.incidentNear v e) := by
  obtain ⟨k,hk,h⟩ := P.incident_segment v e
  have hs := P.step e.val k hk
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simpa only [h0,h1] using hs
  · simpa only [h0,h1] using hs.symm

theorem incidentNear_injective (v : Fin G.n) : Function.Injective (P.incidentNear v) := by
  intro e f heq
  by_contra hef
  have hef' : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  obtain ⟨i,hi,hei⟩ := P.incident_segment v e
  obtain ⟨j,hj,hfj⟩ := P.incident_segment v f
  have hd := P.edges_disjoint e.val f.val hef' i j hi hj
  rcases hei with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> rcases hfj with ⟨g0,g1⟩ | ⟨g0,g1⟩
  · exact hd.1 ⟨h0.trans g0.symm,h1.trans (heq.trans g1.symm)⟩
  · exact hd.2 ⟨h0.trans g1.symm,h1.trans (heq.trans g0.symm)⟩
  · exact hd.2 ⟨h0.trans (heq.trans g1.symm),h1.trans g0.symm⟩
  · exact hd.1 ⟨h0.trans (heq.trans g0.symm),h1.trans g1.symm⟩

def incidentDirection (v : Fin G.n) (e : P.Incident v) : Fin 4 :=
  qmaGridNeighborIndex (P.position v) (P.incidentNear v e)

theorem incidentDirection_injective (v : Fin G.n) : Function.Injective (P.incidentDirection v) := by
  intro e f h
  apply P.incidentNear_injective v
  have hp := P.incident_position_positive v e
  have hh := congrArg (qmaGridNeighbor (P.position v)) h
  exact (qmaGridNeighborIndex_spec hp.1 hp.2 (P.incident_adjacent v e)).symm.trans
    (hh.trans (qmaGridNeighborIndex_spec hp.1 hp.2 (P.incident_adjacent v f)))

include P in
theorem degree_le_four (v : Fin G.n) : qmaGraphDegree G.left G.right v ≤ 4 := by
  have hcard := Fintype.card_le_of_injective (P.incidentDirection v) (P.incidentDirection_injective v)
  have heq : Fintype.card (P.Incident v) = qmaGraphDegree G.left G.right v := by
    rw [Fintype.card_eq_sum_ones]
    exact qmaSumSubtypePredicate (fun e => G.left e = v ∨ G.right e = v) (fun _ => (1 : ℕ))
  simpa only [heq,Fintype.card_fin] using hcard

end QMAPlanarRouteData
end ContinuumCoulomb

end

end OAI
