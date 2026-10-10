import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathVisitCorrectness

namespace OAI

/-! The finite lists of actual routes produce a routing table with exactly
the permissions of the physical graph proof. Lists may use any complete edge
order; this does not change a routing decision. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingTable QuantumPathVisitProgram
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def listedVisits (es : List G.Edge) : List Visit :=
  es.flatMap (fun e => visits (P.routeList e))

 theorem listedVisits_mem (es : List G.Edge) (hcover : ∀ e, e ∈ es) (v : Visit) :
    v ∈ P.listedVisits es ↔ v ∈ P.routingTable.2.1 := by
  change v ∈ P.listedVisits es ↔ v ∈ P.routingVisits
  simp only [listedVisits,List.mem_flatMap,P.routeList_visits_general,routingVisits,
    Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,_,j,hj⟩
    exact ⟨⟨e,j⟩,hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.1,hcover i.1,i.2,hi⟩

end QMAPortRouteData
namespace QuantumPathTable

abbrev Input := List Pair × List (List Pair)
def inputCode : Input → List Bool :=
  prodCode (listCode pairCode) (listCode (listCode pairCode))

def inputVisits (x : Input) : List Visit := (x.2.map visits).flatten

def beforeCrossings (x : Input) : Table := (x.1,inputVisits x,[])

def compile (x : Input) : Table := computedTable (beforeCrossings x)

noncomputable def compileProgram : Procedure inputCode tableCode compile := by
  let sources := Procedure.first (listCode pairCode) (listCode (listCode pairCode))
  let paths := Procedure.second (listCode pairCode) (listCode (listCode pairCode))
  let vs := (QuantumRawExchange.flattenProgram visitCode ((0,0),(0,0))).comp
    ((Procedure.listMap [] [] visitsProgram).comp paths)
  let base := sources.pair (vs.pair (Procedure.constant inputCode (listCode pairCode) []))
  exact computedTableProgram.comp base

 theorem beforeCrossings_visits {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (v : Visit) :
    v ∈ (beforeCrossings (List.ofFn P.position,es.map P.routeList)).2.1 ↔
      v ∈ P.routingTable.2.1 := by
  change v ∈ ((es.map P.routeList).map visits).flatten ↔ _
  rw [List.map_map]
  exact P.listedVisits_mem es hcover v

 theorem compile_crossings {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (p : Pair) :
    p ∈ (compile (List.ofFn P.position,es.map P.routeList)).2.2 ↔ P.IsCrossing p := by
  change p ∈ computedCrossings (beforeCrossings (List.ofFn P.position,es.map P.routeList)) ↔ _
  rw [mem_computedCrossings]
  simp only [crossingTest,Bool.and_eq_true,decide_eq_true_eq,
    beforeCrossings_visits P es hcover]
  exact (P.crossing_iff_opposite_visits p).symm

 theorem compile_allowed {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (es : List G.Edge) (hcover : ∀ e, e ∈ es) (R : QMACellRouteBody) :
    allowed (compile (List.ofFn P.position,es.map P.routeList)) R = allowed P.routingTable R := by
  let x := (List.ofFn P.position,es.map P.routeList)
  have hc (p : Pair) : decide (p ∈ (compile x).2.2) = decide (p ∈ P.routingTable.2.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,compile_crossings P es hcover,P.routingTable_crossing,x]
  have hv (v : Visit) : decide (v ∈ (compile x).2.1) = decide (v ∈ P.routingTable.2.1) := by
    apply Bool.eq_iff_iff.mpr
    have hh := beforeCrossings_visits P es hcover v
    constructor
    · intro h; exact decide_eq_true (hh.mp (of_decide_eq_true h))
    · intro h; exact decide_eq_true (hh.mpr (of_decide_eq_true h))
  have hs (p : Pair) : decide (p ∈ (compile x).1) = decide (p ∈ P.routingTable.1) := rfl
  change allowed (compile x) R = _
  cases R <;> simp only [allowed,hc,hv,hs]

end QuantumPathTable
end ContinuumCoulomb

end

end OAI
