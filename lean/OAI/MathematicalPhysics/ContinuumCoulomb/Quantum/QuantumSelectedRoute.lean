import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteSelectorCorrectness

namespace OAI

/-! The literal route selector returns a permitted catalog path for any
oriented pair of endpoints for which such a path exists. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open QuantumRouteSelectorProgram QuantumTaggedRouteProgram QuantumFiniteRouteSearch

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def HasAllowedRoute (x y : ℕ × ℕ) : Prop :=
  ∃ R : QMACellRoute, P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = x ∧ R.target = y

def findAllowedRoute (x y : ℕ × ℕ) : Option QMACellRoute :=
  (qmaRouteCandidates x y).find? (fun R =>
    decide (P.RoutingAllowed R.body ∧ R.Valid ∧ R.source = x ∧ R.target = y))

theorem findAllowedRoute_isSome {x y : ℕ × ℕ} (h : P.HasAllowedRoute x y) :
    (P.findAllowedRoute x y).isSome := by
  obtain ⟨R,ha,hv,hs,ht⟩ := h
  apply List.find?_isSome.mpr
  refine ⟨R,?_,decide_eq_true ⟨ha,hv,hs,ht⟩⟩
  simpa only [hs,ht] using qmaRouteCandidates_complete R

def selectedAllowedRoute (x y : ℕ × ℕ) (h : P.HasAllowedRoute x y) : QMACellRoute :=
  (P.findAllowedRoute x y).get (P.findAllowedRoute_isSome h)

theorem selectedAllowedRoute_spec (x y : ℕ × ℕ) (h : P.HasAllowedRoute x y) :
    P.RoutingAllowed (P.selectedAllowedRoute x y h).body ∧
      (P.selectedAllowedRoute x y h).Valid ∧
      (P.selectedAllowedRoute x y h).source = x ∧
      (P.selectedAllowedRoute x y h).target = y := by
  have he : P.findAllowedRoute x y = some (P.selectedAllowedRoute x y h) :=
    (Option.some_get (P.findAllowedRoute_isSome h)).symm
  unfold findAllowedRoute at he
  have hp := List.find?_some he
  exact of_decide_eq_true hp

theorem selectedAllowedRoute_path (x y : ℕ × ℕ) (h : P.HasAllowedRoute x y) :
    QuantumRouteSelectorProgram.value (P.routingTable,(x,y)) =
      (P.selectedAllowedRoute x y h).path := by
  have hf : (qmaRouteCandidates x y).find?
      (fun R => accepts (x,y) (tagged P.routingTable R)) =
        some (P.selectedAllowedRoute x y h) := by
    simp only [P.routing_accepts]
    exact (Option.some_get (P.findAllowedRoute_isSome h)).symm
  have hs := selectParallelValue_eq (false,[]) (qmaRouteCandidates x y)
    (fun R => accepts (x,y) (tagged P.routingTable R)) (tagged P.routingTable)
    (qmaRouteCandidates_length x y) hf
  simpa only [value,choose,candidates,List.map_map,Function.comp_def,tagged]
    using congrArg (fun v : Tagged => v.2) hs

theorem hasAllowedRoute_reverse {x y : ℕ × ℕ} (h : P.HasAllowedRoute x y) :
    P.HasAllowedRoute y x := by
  obtain ⟨R,ha,hv,hs,ht⟩ := h
  exact ⟨R.reverse,ha,hv,R.reverse_source.trans ht,R.reverse_target.trans hs⟩

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
