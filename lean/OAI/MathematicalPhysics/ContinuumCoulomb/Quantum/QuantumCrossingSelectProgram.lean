import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListLayer
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteMembership

namespace OAI

/-! Select crossing interactions directly from the finite bond tape.
Both orientations contribute to each rational coupling; every other bond is
retained. All scans are literal polynomial programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode
open QuantumCrossingListBlock

def hits (x : Bond × Pair) : Bool :=
  decide ((x.1.1,x.1.2.1)=x.2) || decide ((x.1.2.1,x.1.1)=x.2)
def terminalPair (a : Fin 2) (s : Sites) : Pair :=
  (site s (if a=0 then 0 else 1),site s (if a=0 then 2 else 3))
def pairs (ss : List Sites) : List Pair :=
  (ss.map (fun s => [terminalPair 0 s,terminalPair 1 s])).flatten
def contribution (x : Bond × Pair) : ℚ := if hits x then x.1.2.2 else 0
def weight (x : List Bond × Pair) : ℚ := (x.1.map (fun e => contribution (e,x.2))).sum
def keep (x : List Pair × Bond) : Bool := !(x.1.any (fun p => hits (x.2,p)))
def retained (x : List Pair × List Bond) : List Bond := x.2.filter (fun e => keep (x.1,e))
def crossing (x : List Bond × Sites) : Crossing :=
  ((weight (x.1,terminalPair 0 x.2),weight (x.1,terminalPair 1 x.2)),x.2)
def crossings (x : List Bond × List Sites) : List Crossing := x.2.map (fun s => crossing (x.1,s))

noncomputable opaque hitsProgram : Procedure (prodCode bondCode pairCode) Procedure.boolCode hits := by
  let e := Procedure.first bondCode pairCode
  let p := Procedure.second bondCode pairCode
  let l := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp e
  let r := (Procedure.first Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp e)
  exact Procedure.boolOr.comp
    ((QuantumFiniteMembership.pairEqProgram.comp ((l.pair r).pair p)).pair
      (QuantumFiniteMembership.pairEqProgram.comp ((r.pair l).pair p)))

noncomputable opaque terminalProgram (a : Fin 2) : Procedure sitesCode pairCode (terminalPair a) := by
  let input : Procedure sitesCode QuantumCrossingListBlock.inputCode
      (fun s => ((0,0),0,(0,0),s)) :=
    (Procedure.constant sitesCode parametersCode (0,0)).pair
      ((Procedure.constant sitesCode unaryCode 0).pair
        ((Procedure.constant sitesCode (prodCode ratCode ratCode) (0,0)).pair
          (Procedure.identity sitesCode)))
  exact ((siteProgram (if a=0 then 0 else 1)).comp input).pair
    ((siteProgram (if a=0 then 2 else 3)).comp input)

noncomputable opaque pairsProgram : Procedure (listCode sitesCode) (listCode pairCode) pairs := by
  let entry := (Procedure.listCons pairCode).comp ((terminalProgram 0).pair
    ((Procedure.listCons pairCode).comp ((terminalProgram 1).pair
      (Procedure.constant sitesCode (listCode pairCode) []))))
  exact (QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (Procedure.listMap ((0,0),(0,0)) [] entry)

noncomputable opaque contributionProgram :
    Procedure (prodCode bondCode pairCode) ratCode contribution := by
  let e := Procedure.first bondCode pairCode
  let w := (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp e)
  exact Procedure.conditional hitsProgram w (Procedure.constant _ ratCode 0)

noncomputable opaque weightProgram : Procedure (prodCode (listCode bondCode) pairCode) ratCode weight := by
  let ctx := Procedure.second (listCode bondCode) pairCode
  let es := Procedure.first (listCode bondCode) pairCode
  let term : Procedure (prodCode pairCode bondCode) ratCode
      (fun x => contribution (x.2,x.1)) :=
    contributionProgram.comp ((Procedure.second pairCode bondCode).pair
      (Procedure.first pairCode bondCode))
  exact RationalSumProgram.sumProgram.comp
    ((Procedure.listMapWith (f := fun p e => contribution (e,p)) zeroBond 0 term).comp
      (ctx.pair es))

noncomputable opaque keepProgram : Procedure (prodCode (listCode pairCode) bondCode)
    Procedure.boolCode keep := by
  let ps := Procedure.first (listCode pairCode) bondCode
  let e := Procedure.second (listCode pairCode) bondCode
  exact (Procedure.boolNot.comp (QuantumFiniteMembership.anyProgram.comp
    ((Procedure.listMapWith (f := fun e p => hits (e,p)) (0,0) false hitsProgram).comp
      (e.pair ps)))).congrFun (by
        intro x
        simp only [Function.comp_apply,List.any_map,Function.comp_def,id_eq,keep])

noncomputable opaque retainedProgram :
    Procedure (prodCode (listCode pairCode) (listCode bondCode)) (listCode bondCode) retained := by
  let entry := Procedure.conditional keepProgram
    ((Procedure.listCons bondCode).comp ((Procedure.second (listCode pairCode) bondCode).pair
      (Procedure.constant _ (listCode bondCode) [])))
    (Procedure.constant _ (listCode bondCode) [])
  refine ((QuantumRawExchange.flattenProgram bondCode zeroBond).comp
    (Procedure.listMapWith (f := fun ps e => if keep (ps,e) then [e] else [])
      zeroBond [] entry)).congrFun ?_
  intro x
  change (x.2.map (fun e => if keep (x.1,e) then [e] else [])).flatten =
    x.2.filter (fun e => keep (x.1,e))
  induction x.2 with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.flatten_cons,List.filter_cons] at *
    cases h : keep (x.1,e) <;> simpa [h] using ih

noncomputable opaque crossingProgram : Procedure (prodCode (listCode bondCode) sitesCode)
    crossingCode crossing := by
  let es := Procedure.first (listCode bondCode) sitesCode
  let s := Procedure.second (listCode bondCode) sitesCode
  exact ((weightProgram.comp (es.pair ((terminalProgram 0).comp s))).pair
    (weightProgram.comp (es.pair ((terminalProgram 1).comp s)))).pair s

noncomputable opaque crossingsProgram :
    Procedure (prodCode (listCode bondCode) (listCode sitesCode)) (listCode crossingCode) crossings :=
  Procedure.listMapWith (f := fun es s => crossing (es,s)) ((0,0),(0,0)) zeroCrossing crossingProgram

theorem hits_iff (e : Bond) (p : Pair) :
    hits (e,p)=true ↔ (e.1,e.2.1)=p ∨ (e.2.1,e.1)=p := by
  simp only [hits,Bool.or_eq_true,decide_eq_true_eq]

theorem keep_iff (ps : List Pair) (e : Bond) :
    keep (ps,e)=true ↔ ∀ p ∈ ps, (e.1,e.2.1)≠p ∧ (e.2.1,e.1)≠p := by
  simp only [keep,Bool.not_eq_true_eq_eq_false,List.any_eq_false,hits_iff,not_or]

theorem retained_mem (x : List Pair × List Bond) (e : Bond) :
    e ∈ retained x ↔ e ∈ x.2 ∧ ∀ p ∈ x.1, (e.1,e.2.1)≠p ∧ (e.2.1,e.1)≠p := by
  simp only [retained,List.mem_filter,keep_iff]

theorem retained_bounded {n : ℕ} (ps : List Pair) (es : List Bond)
    (hb : SourceBondLists.bounded n es) : SourceBondLists.bounded n (retained (ps,es)) := by
  intro e he
  exact hb e ((retained_mem (ps,es) e).mp he).1

theorem retained_noLoops (ps : List Pair) (es : List Bond)
    (hn : ∀ e ∈ es, e.1 ≠ e.2.1) : ∀ e ∈ retained (ps,es), e.1 ≠ e.2.1 := by
  intro e he
  exact hn e ((retained_mem (ps,es) e).mp he).1

abbrev Input := ℚ × (QuantumListPathStep.Output × List Sites)
def inputCode : Input → List Bool :=
  prodCode ratCode (prodCode QuantumListPathStep.outputCode (listCode sitesCode))
def value (x : Input) : QuantumCrossingListLayer.Input :=
  ((x.1,x.2.1.1,retained (pairs x.2.2,x.2.1.2.1),x.2.1.2.2),
    crossings (x.2.1.2.1,x.2.2))

noncomputable opaque precisionProgram : Procedure inputCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque packetProgram :
    Procedure inputCode QuantumListPathStep.outputCode (fun x => x.2.1) :=
  (Procedure.first QuantumListPathStep.outputCode (listCode sitesCode)).comp
    (Procedure.second ratCode (prodCode QuantumListPathStep.outputCode (listCode sitesCode)))
noncomputable opaque sitesProgram : Procedure inputCode (listCode sitesCode) (fun x => x.2.2) :=
  (Procedure.second QuantumListPathStep.outputCode (listCode sitesCode)).comp
    (Procedure.second ratCode (prodCode QuantumListPathStep.outputCode (listCode sitesCode)))
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) (fun x => x.2.1.2.1) :=
  (Procedure.first (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram)
noncomputable opaque program :
    Procedure inputCode QuantumCrossingListLayer.inputCode value := by
  let n := (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
  let c := (Procedure.second (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram)
  let es := retainedProgram.comp ((pairsProgram.comp sitesProgram).pair bondsProgram)
  let cs := crossingsProgram.comp (bondsProgram.pair sitesProgram)
  exact (precisionProgram.pair (n.pair (es.pair c))).pair cs

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
