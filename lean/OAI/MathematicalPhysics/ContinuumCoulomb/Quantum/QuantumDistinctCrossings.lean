import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPairDedup
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathTable

namespace OAI

/-! The actual finite crossing list, with duplicates removed, enumerates
each physical crossing cell exactly once. -/

noncomputable section
namespace ContinuumCoulomb.QuantumDistinctCrossings
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open scoped Classical

def value (x : QuantumPathTable.Input) : List Pair :=
  (QuantumPathTable.compile x).2.2.dedup

noncomputable opaque program :
    Procedure QuantumPathTable.inputCode (listCode pairCode) value :=
  QuantumPairDedup.program.comp
    (((Procedure.second (listCode QuantumRoutingTable.visitCode) (listCode pairCode)).comp
      (Procedure.second (listCode pairCode)
        (prodCode (listCode QuantumRoutingTable.visitCode) (listCode pairCode)))).comp
      QuantumPathTable.compileProgram)

theorem nodup (x : QuantumPathTable.Input) : (value x).Nodup := List.nodup_dedup _

theorem mem_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (p : Pair) :
    p ∈ value (List.ofFn P.position,es.map P.routeList) ↔ P.IsCrossing p := by
  rw [value,List.mem_dedup]
  exact QuantumPathTable.compile_crossings P es hcover p

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es)

def cell (i : Fin (value (List.ofFn P.position,es.map P.routeList)).length) : P.Crossing :=
  ⟨(value (List.ofFn P.position,es.map P.routeList)).get i,
    P.mem_crossingCells.mpr ((mem_actual P es hcover _).mp (List.get_mem _ i))⟩

theorem cell_bijective : Function.Bijective (cell P es hcover) := by
  constructor
  · intro i j hij
    exact (nodup _).injective_get (congrArg Subtype.val hij)
  · intro c
    have hc : c.val ∈ value (List.ofFn P.position,es.map P.routeList) :=
      (mem_actual P es hcover _).mpr (P.mem_crossingCells.mp c.property)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
    exact ⟨i,Subtype.ext hi⟩

def cellsEquiv : Fin (value (List.ofFn P.position,es.map P.routeList)).length ≃ P.Crossing :=
  Equiv.ofBijective (cell P es hcover) (cell_bijective P es hcover)

theorem list_eq : value (List.ofFn P.position,es.map P.routeList)=
    List.ofFn (fun i => (cellsEquiv P es hcover i).val) :=
  (List.ofFn_get _).symm

end ContinuumCoulomb.QuantumDistinctCrossings

end

end OAI
