import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPathProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawProgram

namespace OAI

/-! Literal polynomial evaluation of all 140 path candidates. Every template
is constant-sized, and only its endpoint cell coordinates vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCellPathProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

private noncomputable def appendPaths {f g : Pair → List (List Pair)}
    (p : Procedure pairCode (listCode (listCode pairCode)) f)
    (q : Procedure pairCode (listCode (listCode pairCode)) g) :
    Procedure pairCode (listCode (listCode pairCode)) (fun x => f x++g x) :=
  (Procedure.listAppend (listCode pairCode) []).comp (p.pair q)

private noncomputable def singletonPath {f : Pair → List Pair}
    (p : Procedure pairCode (listCode pairCode) f) :
    Procedure pairCode (listCode (listCode pairCode)) (fun x => [f x]) :=
  (Procedure.listCons (listCode pairCode)).comp
    (p.pair (Procedure.constant pairCode (listCode (listCode pairCode)) []))

noncomputable def flatFamilyProgram (m : ℕ) (f : Fin m → Pair → List (List Pair))
    (p : ∀ i, Procedure pairCode (listCode (listCode pairCode)) (f i)) :
    Procedure pairCode (listCode (listCode pairCode))
      (fun x => (List.ofFn (fun i => f i x)).flatten) := by
  induction m with
  | zero => exact (Procedure.constant _ _ []).congrFun (by intro x; simp)
  | succ m ih =>
    exact (appendPaths (p 0) (ih (fun i => f i.succ) (fun i => p i.succ))).congrFun (by
      intro x
      simp only [List.ofFn_succ,List.flatten_cons])

noncomputable opaque corridorBlockProgram (a : Fin 4) :
    Procedure pairCode (listCode (listCode pairCode)) (fun p =>
      [(QMACellRouteBody.corridor p a false false).path,
       (QMACellRouteBody.corridor p a false true).path,
       (QMACellRouteBody.corridor p a true false).path,
       (QMACellRouteBody.corridor p a true true).path]) :=
  (appendPaths
    (appendPaths (singletonPath (corridorProgram a false false)) (singletonPath (corridorProgram a false true)))
    (appendPaths (singletonPath (corridorProgram a true false)) (singletonPath (corridorProgram a true true)))).congrFun
      (by intro p; rfl)

noncomputable opaque bodyPathsProgram : Procedure pairCode (listCode (listCode pairCode))
    (fun p => (qmaCellBodies p).map QMACellRouteBody.path) := by
  let rays := QuantumRawExchange.fixedListProgram pairCode (listCode pairCode) 4 _ rayProgram
  let pairs := QuantumRawExchange.fixedListProgram pairCode (listCode pairCode) 6 _ pairProgram
  let patches := QuantumRawExchange.fixedListProgram pairCode (listCode pairCode) 9 _ patchProgram
  let corridors := flatFamilyProgram 4 _ corridorBlockProgram
  exact (appendPaths (appendPaths (appendPaths rays pairs) patches) corridors).congrFun (by
    intro p
    simp only [qmaCellBodies,List.map_append,List.ofFn_eq_map,List.map_map,
      List.flatMap_def,List.map_flatten,List.map_cons,List.map_nil,Function.comp_def])

noncomputable opaque orientedPathProgram : Procedure (listCode pairCode) (listCode (listCode pairCode))
    (fun xs => [xs,xs.reverse]) :=
  ((Procedure.listCons (listCode pairCode)).comp
    ((Procedure.identity (listCode pairCode)).pair
      ((Procedure.listCons (listCode pairCode)).comp
        ((Procedure.listReverse pairCode (0,0)).pair
          (Procedure.constant (listCode pairCode) (listCode (listCode pairCode)) [])))))

noncomputable opaque bodyAtProgram (i : Fin 35) : Procedure pairCode (listCode pairCode)
    (fun p => (((qmaCellBodies p).map QMACellRouteBody.path).drop i.val).headD []) :=
  (Procedure.listGet (listCode pairCode) []).comp
    ((Procedure.constant pairCode Nat.bits i.val).pair bodyPathsProgram)

private theorem ofFn_headD_map {α β : Type} (xs : List α) (default : α) (f : α → β) :
    (List.ofFn (fun i : Fin xs.length => f ((xs.drop i.val).headD default))) = xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < xs.length := by simpa using hi
    simp only [List.getElem_ofFn,List.getElem_map]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem h,Option.getD_some]

noncomputable opaque cellPathsProgram : Procedure pairCode (listCode (listCode pairCode))
    (fun p => (qmaCellRoutes p).map QMACellRoute.path) :=
  (flatFamilyProgram 35 _ (fun i => orientedPathProgram.comp (bodyAtProgram i))).congrFun (by
    intro p
    have hlen : ((qmaCellBodies p).map QMACellRouteBody.path).length = 35 := by
      simp only [List.length_map,qmaCellBodies_length]
    have h := ofFn_headD_map ((qmaCellBodies p).map QMACellRouteBody.path) []
      (fun xs => [xs,xs.reverse])
    rw [hlen] at h
    simp only [Function.comp_apply]
    rw [h]
    simp only [qmaCellRoutes,List.flatMap_def,List.map_flatten,List.map_map,
      Function.comp_def,List.map_cons,List.map_nil,QMACellRoute.path,Bool.false_eq_true,
      ite_false,ite_true])

abbrev Endpoints := Pair × Pair
def endpointsCode : Endpoints → List Bool := prodCode pairCode pairCode

noncomputable opaque pointCellProgram : Procedure pairCode pairCode qmaPointCell := by
  let c := Procedure.constant pairCode Nat.bits 32
  exact (Procedure.binaryDiv.comp ((Procedure.first Nat.bits Nat.bits).pair c)).pair
    (Procedure.binaryDiv.comp ((Procedure.second Nat.bits Nat.bits).pair c))

noncomputable opaque candidatePathsProgram : Procedure endpointsCode (listCode (listCode pairCode))
    (fun x => (qmaRouteCandidates x.1 x.2).map QMACellRoute.path) := by
  let left := cellPathsProgram.comp (pointCellProgram.comp (Procedure.first pairCode pairCode))
  let right := cellPathsProgram.comp (pointCellProgram.comp (Procedure.second pairCode pairCode))
  exact ((Procedure.listAppend (listCode pairCode) []).comp (left.pair right)).congrFun (by
    intro x
    simp only [qmaRouteCandidates,List.map_append,Function.comp_apply])

end ContinuumCoulomb.QuantumCellPathProgram

end

end OAI
