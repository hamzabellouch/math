import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteSelectorProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingTableCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteCandidates

namespace OAI

/-! The finite data program returns exactly the path used by the actual
merged physical graph, rather than merely a path with the same endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRoutingTable QuantumTaggedRouteProgram QuantumRouteSelectorProgram
open QuantumFiniteRouteSearch

namespace QMACellRoute

theorem headD_path (R : QMACellRoute) : R.path.headD (0,0) = R.source := by
  rw [List.headD_eq_head?_getD,R.endpoints.1]
  rfl

theorem reverse_headD_path (R : QMACellRoute) : R.path.reverse.headD (0,0) = R.target := by
  rw [List.headD_eq_head?_getD,List.head?_reverse,R.endpoints.2]
  rfl

end QMACellRoute

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem routing_accepts (ends : Ends) (R : QMACellRoute) :
    accepts ends (tagged P.routingTable R) =
      decide (P.RoutingAllowed R.body ∧ R.Valid ∧ R.source=ends.1 ∧ R.target=ends.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [accepts,tagged,Bool.and_eq_true,bodyPermitted_eq_true,decide_eq_true_eq,
    P.routingTable_allowed,R.headD_path,R.reverse_headD_path,QMACellRoute.Valid]
  constructor
  · rintro ⟨⟨⟨ha,hv⟩,hs⟩,ht⟩
    exact decide_eq_true ⟨ha,hv,hs,ht⟩
  · intro h
    obtain ⟨ha,hv,hs,ht⟩ := of_decide_eq_true h
    exact ⟨⟨⟨ha,hv⟩,hs⟩,ht⟩

theorem selected_merged_path (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) :
    QuantumRouteSelectorProgram.value (P.routingTable,
      P.crossingPosition N D ((P.crossingOutput N hD).merge.left e),
      P.crossingPosition N D ((P.crossingOutput N hD).merge.right e)) =
        (P.mergedOutputRoute N hD havoid e).path := by
  let ends : Ends :=
    (P.crossingPosition N D ((P.crossingOutput N hD).merge.left e),
     P.crossingPosition N D ((P.crossingOutput N hD).merge.right e))
  have hf : (qmaRouteCandidates ends.1 ends.2).find?
      (fun R => accepts ends (tagged P.routingTable R)) =
        some (P.mergedOutputRoute N hD havoid e) := by
    simp only [P.routing_accepts]
    exact P.mergedOutputRoute_find N hD havoid e
  have h := selectParallelValue_eq (false,[]) (qmaRouteCandidates ends.1 ends.2)
    (fun R => accepts ends (tagged P.routingTable R)) (tagged P.routingTable)
    (qmaRouteCandidates_length ends.1 ends.2) hf
  have hs := congrArg (fun v : Tagged => v.2) h
  simpa only [value,choose,candidates,List.map_map,Function.comp_def,tagged] using hs

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
