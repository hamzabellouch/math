import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteEnumeration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! Literal rational-register-free programs evaluate all four finite cell path
families, including the two translated halves of an external corridor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCellPathProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev TranslateInput := Pair × Pair
def translateCode : TranslateInput → List Bool := prodCode pairCode pairCode

noncomputable opaque translateProgram : Procedure translateCode pairCode
    (fun x => qmaCellTranslate x.1 x.2) := by
  let p := Procedure.first pairCode pairCode
  let z := Procedure.second pairCode pairCode
  let px := (Procedure.first Nat.bits Nat.bits).comp p
  let py := (Procedure.second Nat.bits Nat.bits).comp p
  let zx := (Procedure.first Nat.bits Nat.bits).comp z
  let zy := (Procedure.second Nat.bits Nat.bits).comp z
  let c := Procedure.constant translateCode Nat.bits 32
  let x := Procedure.binaryAdd.comp ((Procedure.binaryMul.comp (c.pair px)).pair zx)
  let y := Procedure.binaryAdd.comp ((Procedure.binaryMul.comp (c.pair py)).pair zy)
  exact (x.pair y).congrFun (by intro x; rfl)

noncomputable opaque translatedPathProgram (xs : List Pair) :
    Procedure pairCode (listCode pairCode) (fun p => xs.map (qmaCellTranslate p)) :=
  (Procedure.listMapWith (0,0) (0,0) translateProgram).comp
    ((Procedure.identity pairCode).pair (Procedure.constant pairCode (listCode pairCode) xs))

noncomputable opaque neighborProgram (a : Fin 4) : Procedure pairCode pairCode
    (fun p => qmaGridNeighbor p a) := by
  let x := Procedure.first Nat.bits Nat.bits
  let y := Procedure.second Nat.bits Nat.bits
  let c := Procedure.constant pairCode Nat.bits 1
  by_cases h0 : a = 0
  · subst a
    exact ((Procedure.binaryAdd.comp (x.pair c)).pair y).congrFun (by intro p; rfl)
  by_cases h1 : a = 1
  · subst a
    exact (x.pair (Procedure.binaryAdd.comp (y.pair c))).congrFun (by intro p; rfl)
  by_cases h2 : a = 2
  · subst a
    exact ((Procedure.binarySub.comp (x.pair c)).pair y).congrFun (by intro p; rfl)
  have h3 : a = 3 := by omega
  subst a
  exact (x.pair (Procedure.binarySub.comp (y.pair c))).congrFun (by intro p; rfl)

noncomputable opaque rayProgram (a : Fin 4) : Procedure pairCode (listCode pairCode)
    (fun p => (QMACellRouteBody.ray p a).path) := translatedPathProgram (qmaCellRayPath a)

noncomputable opaque pairProgram (e : Fin 6) : Procedure pairCode (listCode pairCode)
    (fun p => (QMACellRouteBody.pair p e).path) := translatedPathProgram (qmaCellPairPath e)

noncomputable opaque patchProgram (e : Fin 9) : Procedure pairCode (listCode pairCode)
    (fun p => (QMACellRouteBody.patch p e).path) :=
  (translatedPathProgram (qmaLocalPatchPath e)).congrFun (by
    intro p
    simp only [qmaLocalPatchPath,List.map_map,Function.comp_def,QMACellRouteBody.path,
      qmaCrossingPathAt]
    congr 1
    funext z
    exact qmaCellTranslate_patch p z)

noncomputable opaque halfProgram (a : Fin 4) (b : Bool) : Procedure pairCode (listCode pairCode)
    (fun p => qmaHalfPathAt p b a) := translatedPathProgram (qmaHalfCorridorPath b a)

noncomputable opaque corridorProgram (a : Fin 4) (b c : Bool) :
    Procedure pairCode (listCode pairCode) (fun p => (QMACellRouteBody.corridor p a b c).path) := by
  let first := halfProgram a b
  let second := (Procedure.listReverse pairCode (0,0)).comp
    ((halfProgram (qmaPortOpposite a) c).comp (neighborProgram a))
  exact (Procedure.listAppend pairCode (0,0)).comp (first.pair second)

end ContinuumCoulomb.QuantumCellPathProgram

end

end OAI
