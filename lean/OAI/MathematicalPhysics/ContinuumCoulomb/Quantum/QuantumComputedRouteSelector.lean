import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteSelectorCorrectness

namespace OAI

/-! Route selection directly from source-position and coarse-path lists. The
crossing and permission tables are computed inside the polynomial program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumComputedRouteSelector
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumRouteSelectorProgram QuantumTaggedRouteProgram

abbrev Input := QuantumPathTable.Input × Ends
def inputCode : Input → List Bool := prodCode QuantumPathTable.inputCode endsCode

def value (x : Input) : List Pair :=
  QuantumRouteSelectorProgram.value (QuantumPathTable.compile x.1,x.2)

noncomputable def program : Procedure inputCode (listCode pairCode) value :=
  QuantumRouteSelectorProgram.program.comp
    ((QuantumPathTable.compileProgram.comp (Procedure.first QuantumPathTable.inputCode endsCode)).pair
      (Procedure.second QuantumPathTable.inputCode endsCode))

 theorem value_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (ends : Ends) :
    value ((List.ofFn P.position,es.map P.routeList),ends) =
      QuantumRouteSelectorProgram.value (P.routingTable,ends) := by
  have ht (R : QMACellRoute) :
      tagged (QuantumPathTable.compile (List.ofFn P.position,es.map P.routeList)) R =
        tagged P.routingTable R := by
    simp only [tagged,bodyPermitted,QuantumPathTable.compile_allowed P es hcover]
  unfold value QuantumRouteSelectorProgram.value candidates
  rw [show tagged (QuantumPathTable.compile (List.ofFn P.position,es.map P.routeList)) =
    tagged P.routingTable from funext ht]

 theorem value_merged {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.crossingOutput N hD).merge.Edge) :
    value ((List.ofFn P.position,es.map P.routeList),
      P.crossingPosition N D ((P.crossingOutput N hD).merge.left e),
      P.crossingPosition N D ((P.crossingOutput N hD).merge.right e)) =
        (P.mergedOutputRoute N hD havoid e).path := by
  rw [value_actual P es hcover]
  exact P.selected_merged_path N hD havoid e

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode (listCode pairCode) value :=
  program.toTM2

end ContinuumCoulomb.QuantumComputedRouteSelector

end

end OAI
