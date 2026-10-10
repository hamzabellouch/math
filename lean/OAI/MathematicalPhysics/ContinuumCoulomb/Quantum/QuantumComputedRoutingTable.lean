import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingCrossingTest
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! Compute the crossing list from encoded visits, and preserve exactly the
routing permissions of the geometric construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingTable
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

private theorem filter_eq_flatten {α : Type} (p : α → Bool) (xs : List α) :
    (xs.map (fun a => if p a then [a] else [])).flatten = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.flatten_cons,List.filter_cons,ih]
    cases p a <;> simp

private noncomputable def selectCrossingProgram :
    Procedure inputCode (listCode pairCode)
      (fun x => if crossingTest x.1 x.2 then [x.2] else []) :=
  Procedure.conditional crossingTestProgram
    ((Procedure.listCons pairCode).comp
      (cellProgram.pair (Procedure.constant inputCode (listCode pairCode) [])))
    (Procedure.constant inputCode (listCode pairCode) [])

noncomputable def computedCrossingsProgram : Procedure tableCode (listCode pairCode)
    computedCrossings := by
  let visits : Procedure tableCode (listCode visitCode) (fun t => t.2.1) :=
    (Procedure.first (listCode visitCode) (listCode pairCode)).comp
      (Procedure.second (listCode pairCode) (prodCode (listCode visitCode) (listCode pairCode)))
  let cells := (Procedure.listMap ((0,0),(0,0)) (0,0)
    (Procedure.first pairCode pairCode)).comp visits
  let selected := (Procedure.listMapWith (f := fun t p => if crossingTest t p then [p] else [])
    (0,0) [] selectCrossingProgram).comp ((Procedure.identity tableCode).pair cells)
  exact ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp selected).congrFun (by
    intro t
    change ((t.2.1.map Prod.fst).map (fun p => if crossingTest t p then [p] else [])).flatten = _
    exact filter_eq_flatten (crossingTest t) (t.2.1.map Prod.fst))

def computedTable (t : Table) : Table := (t.1,t.2.1,computedCrossings t)

noncomputable def computedTableProgram : Procedure tableCode tableCode computedTable := by
  let rest := Procedure.second (listCode pairCode) (prodCode (listCode visitCode) (listCode pairCode))
  let visits := (Procedure.first (listCode visitCode) (listCode pairCode)).comp rest
  exact (Procedure.first (listCode pairCode) _).pair (visits.pair computedCrossingsProgram)

 theorem computedTable_allowed {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (R : QMACellRouteBody) :
    allowed (computedTable P.routingTable) R = allowed P.routingTable R := by
  have h (p : Pair) : p ∈ computedCrossings P.routingTable ↔
      p ∈ P.routingTable.2.2 :=
    (computedCrossings_correct P p).trans (P.routingTable_crossing p).symm
  apply Bool.eq_iff_iff.mpr
  cases R with
  | ray p a =>
    simp only [allowed,computedTable,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,
      decide_eq_true_eq,decide_eq_false_iff_not,h]
    constructor
    · rintro ⟨hs,hc⟩; exact ⟨of_decide_eq_true hs,hc⟩
    · rintro ⟨hs,hc⟩; exact ⟨decide_eq_true hs,hc⟩
  | pair p e =>
    simp only [allowed,computedTable,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,
      decide_eq_true_eq,decide_eq_false_iff_not,h]
    constructor
    · rintro ⟨hc,hv⟩; exact ⟨hc,of_decide_eq_true hv⟩
    · rintro ⟨hc,hv⟩; exact ⟨hc,decide_eq_true hv⟩
  | patch p e => simp only [allowed,computedTable,decide_eq_true_eq,h]
  | corridor p a b c =>
    cases b <;> cases c <;> simp [allowed,computedTable,h]

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
