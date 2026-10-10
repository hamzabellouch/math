import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedArms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.BitStackUnary

namespace OAI

/-! Literal evaluation and enumeration of the three buffered endpoint arms.
The lane color is unary, as required by the polynomial geometric size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedArmProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

private noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Nat.bits (fun x => f x+g x) := Procedure.binaryAdd.comp (p.pair q)
private noncomputable def sub {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Nat.bits (fun x => f x-g x) := Procedure.binarySub.comp (p.pair q)
private noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Nat.bits (fun x => f x*g x) := Procedure.binaryMul.comp (p.pair q)
private noncomputable def le {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea Nat.bits f) (q : Procedure ea Nat.bits g) :
    Procedure ea Procedure.boolCode (fun x => decide (f x ≤ g x)) :=
  Procedure.binaryLe.comp (p.pair q)

private noncomputable def u : Procedure axisCode Nat.bits (fun x => x.1.1) := axisStartProgram
private noncomputable def v : Procedure axisCode Nat.bits (fun x => x.1.2) := axisEndProgram
private noncomputable def k : Procedure axisCode Nat.bits (fun x => x.2) := axisCursorProgram
private noncomputable def c (n : ℕ) : Procedure axisCode Nat.bits (fun _ => n) :=
  Procedure.constant _ _ n

noncomputable def doglegProgram : Procedure axisCode pairCode
    (fun x => qmaBufferedDoglegPoint x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (le k (sub v (c 17))) ((add (c 17) k).pair (c 17))
    (Procedure.conditional (le k (add (sub v (c 17)) (sub u (c 17))))
      (v.pair (add (c 17) (sub k (sub v (c 17))))) (u.pair u))).congrFun (by
        intro x
        simp only [qmaBufferedDoglegPoint,decide_eq_true_eq])

noncomputable def detourProgram : Procedure axisCode pairCode
    (fun x => qmaBufferedDetourPoint x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (le k (c 8)) ((sub (c 17) k).pair (c 17))
    (Procedure.conditional (le k u) ((c 9).pair (add k (c 9)))
      (Procedure.conditional (le k (sub (add u v) (c 9)))
        ((add (sub k u) (c 9)).pair (add u (c 9)))
        (Procedure.conditional (le k (add u v))
          (v.pair (sub (add (mul (c 2) u) v) k)) (u.pair u))))).congrFun (by
            intro x
            simp only [qmaBufferedDetourPoint,decide_eq_true_eq])

def point (a : Fin 3) (color j : ℕ) : Pair :=
  let u := 8*(color+3)
  if a = 0 then qmaBufferedDoglegPoint u (u-1) j
  else if a = 1 then (qmaBufferedDoglegPoint u (u-1) j).swap
  else qmaBufferedDetourPoint u (u-1) j

def length (a : Fin 3) (color : ℕ) : ℕ :=
  if a = 2 then 16*color+48 else 16*color+14

 theorem point_eq (colors : Fin 3 → ℕ) (a : Fin 3) (j : ℕ) :
    qmaBufferedArmPoint colors (fun _ => false) a j = point a (colors a) j := rfl

 theorem length_eq (colors : Fin 3 → ℕ) (a : Fin 3) :
    qmaBufferedArmLength colors (fun _ => false) a = length a (colors a) := by
  simp only [qmaBufferedArmLength,qmaBufferedPort,qmaBufferedOffset,Bool.false_eq_true,
    ite_false,length,qmaBufferedDoglegLength]
  split_ifs <;> omega

noncomputable def pointProgram (a : Fin 3) :
    Procedure (prodCode unaryCode Nat.bits) pairCode (fun x => point a x.1 x.2) := by
  let en := prodCode unaryCode Nat.bits
  let color := Procedure.unaryToBits.comp (Procedure.first unaryCode Nat.bits)
  let port := mul (Procedure.constant en Nat.bits 8)
    (add color (Procedure.constant en Nat.bits 3))
  let arg := (port.pair (sub port (Procedure.constant en Nat.bits 1))).pair
    (Procedure.second unaryCode Nat.bits)
  let dog := doglegProgram.comp arg
  by_cases ha : a=0
  · exact dog.congrFun (by intro x; simp [point,ha])
  · by_cases hb : a=1
    · exact (Procedure.swap Nat.bits Nat.bits |>.comp dog).congrFun (by
        intro x; simp [point,hb])
    · exact (detourProgram.comp arg).congrFun (by
        intro x; simp [point,ha,hb])

noncomputable def lengthProgram (a : Fin 3) : Procedure unaryCode unaryCode (length a) :=
  (Procedure.unaryAdd.comp
    ((Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode 16).pair
      (Procedure.identity unaryCode))).pair
        (Procedure.constant unaryCode unaryCode (if a=2 then 48 else 14)))).congrFun (by
          intro color
          simp only [Function.comp_apply,id_eq,length]
          split_ifs <;> rfl)

noncomputable def listProgram (a : Fin 3) : Procedure unaryCode (listCode pairCode)
    (fun color => (List.range (length a color+1)).map (point a color)) := by
  let step := (pointProgram a).comp ((Procedure.second unaryCode unaryCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)))
  let all := Procedure.tabulate (0,0) step
  let n := Procedure.unarySuccessor.comp (lengthProgram a)
  exact all.comp (n.pair (Procedure.identity unaryCode))

end ContinuumCoulomb.QuantumBufferedArmProgram

end

end OAI
