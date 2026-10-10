import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalCrossing
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathScaleProgram

namespace OAI

/-! Exact rational scale for a simultaneous crossing layer, computed from
its retained coefficients and the two crossing coefficients at each cell. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

abbrev Pair := ℚ × ℚ
def pairCode : Pair → List Bool := prodCode ratCode ratCode
abbrev Input := (ℚ × ℚ) × (List ℚ × List Pair)
def inputCode : Input → List Bool :=
  prodCode pairCode (prodCode (listCode ratCode) (listCode pairCode))
def linearCost (p : Pair) : ℚ := 1+|p.1|+|p.2|
def squareCost (p : Pair) : ℚ := (linearCost p)^2
def base (x : Input) : ℚ := 3*(x.2.1.map abs).sum+|x.1.2|
def active (x : Input) : ℚ := 6*(x.2.2.map linearCost).sum
def correction (x : Input) : ℚ := base x+12*(x.2.2.map squareCost).sum
def value (x : Input) : ℚ :=
  16*(active x+correction x+1)^3*x.1.1+4*(active x+correction x+1)+1

noncomputable opaque linearProgram : Procedure pairCode ratCode linearCost :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant pairCode ratCode 1).pair
      (MediatorProgram.absoluteProgram.comp (Procedure.first ratCode ratCode)))).pair
    (MediatorProgram.absoluteProgram.comp (Procedure.second ratCode ratCode)))
noncomputable opaque squareProgram : Procedure pairCode ratCode squareCost :=
  QuantumRoutingCode.squareProgram linearProgram
noncomputable def sumMapProgram {f : Pair → ℚ} (p : Procedure pairCode ratCode f) :
    Procedure (listCode pairCode) ratCode (fun xs => (xs.map f).sum) :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap (0,0) 0 p)
noncomputable opaque program : Procedure inputCode ratCode value := by
  let params := Procedure.first pairCode (prodCode (listCode ratCode) (listCode pairCode))
  let lists := Procedure.second pairCode (prodCode (listCode ratCode) (listCode pairCode))
  let n := (Procedure.first ratCode ratCode).comp params
  let c := (Procedure.second ratCode ratCode).comp params
  let retained := (Procedure.first (listCode ratCode) (listCode pairCode)).comp lists
  let selected := (Procedure.second (listCode ratCode) (listCode pairCode)).comp lists
  let b := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair
      ((QuantumPathScaleProgram.sumMapProgram MediatorProgram.absoluteProgram).comp retained))).pair
      (MediatorProgram.absoluteProgram.comp c))
  let a := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 6).pair
    ((sumMapProgram linearProgram).comp selected))
  let d := Procedure.ratAdd.comp (b.pair
    (Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 12).pair
      ((sumMapProgram squareProgram).comp selected))))
  exact QuantumRoutingCode.scaleProgram.comp (a.pair (d.pair n))

def actualInput {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : Input :=
  ((N,C.base.constant),(List.ofFn (fun i => C.base.weight (labels.symm i)),
    List.ofFn (fun i => (C.J i,C.K i))))

theorem value_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : value (actualInput C N labels)=C.scale N := by
  simp only [value,base,active,correction,actualInput,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,linearCost,squareCost,QMARationalCrossingLayer.scale]
  rw [labels.symm.sum_comp (fun e => |C.base.weight e|)]

end ContinuumCoulomb.QuantumCrossingScaleProgram

end

end OAI
