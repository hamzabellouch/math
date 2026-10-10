import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteSelectorProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathTable

namespace OAI

/-! The route selector depends on permission bits, independently of the
order in which the finite table records the same geometry. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteSelectorProgram
open scoped Classical
open QuantumRoutingTable QuantumTaggedRouteProgram

theorem value_congr {t u : Table} (h : ∀ B, allowed t B = allowed u B)
    (ends : Ends) : value (t,ends) = value (u,ends) := by
  have ht : tagged t = tagged u := by
    funext R
    change (allowed t R.body && decide R.body.Valid,R.path) =
      (allowed u R.body && decide R.body.Valid,R.path)
    rw [h]
  simp only [value,candidates,ht]

theorem compiled_value {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (ends : Ends) :
    value (QuantumPathTable.compile (List.ofFn P.position,es.map P.routeList),ends) =
      value (P.routingTable,ends) :=
  value_congr (QuantumPathTable.compile_allowed P es hcover) ends

end ContinuumCoulomb.QuantumRouteSelectorProgram

end

end OAI
