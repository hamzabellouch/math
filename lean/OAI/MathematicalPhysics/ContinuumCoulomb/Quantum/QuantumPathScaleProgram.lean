import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalPathStep
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram

namespace OAI

/-! Exact rational calibration from the retained and selected edge weights.
The sums are computed by the proved polynomial rational-list accumulator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPathScaleProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

abbrev Input := (ℚ × ℚ) × (List ℚ × List ℚ)
def inputCode : Input → List Bool :=
  prodCode (prodCode ratCode ratCode) (prodCode (listCode ratCode) (listCode ratCode))

def linearCost (w : ℚ) : ℚ := 1+2*|w|
def squareCost (w : ℚ) : ℚ := (1+|w|)^2
def base (x : Input) : ℚ := 3*(x.2.1.map abs).sum+|x.1.2|
def active (x : Input) : ℚ := 3*(x.2.2.map linearCost).sum
def correction (x : Input) : ℚ := base x+4*(x.2.2.map squareCost).sum
def value (x : Input) : ℚ :=
  16*(active x+correction x+1)^3*x.1.1+4*(active x+correction x+1)+1

noncomputable def linearProgram : Procedure ratCode ratCode linearCost :=
  Procedure.ratAdd.comp ((Procedure.constant ratCode ratCode 1).pair
    (Procedure.ratMul.comp ((Procedure.constant ratCode ratCode 2).pair
      MediatorProgram.absoluteProgram)))

noncomputable def squareProgram : Procedure ratCode ratCode squareCost :=
  QuantumRoutingCode.squareProgram (Procedure.ratAdd.comp
    ((Procedure.constant ratCode ratCode 1).pair MediatorProgram.absoluteProgram))

noncomputable def sumMapProgram {f : ℚ → ℚ} (p : Procedure ratCode ratCode f) :
    Procedure (listCode ratCode) ratCode (fun xs => (xs.map f).sum) :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap 0 0 p)

noncomputable def program : Procedure inputCode ratCode value := by
  let params := Procedure.first (prodCode ratCode ratCode)
    (prodCode (listCode ratCode) (listCode ratCode))
  let lists := Procedure.second (prodCode ratCode ratCode)
    (prodCode (listCode ratCode) (listCode ratCode))
  let n := (Procedure.first ratCode ratCode).comp params
  let c := (Procedure.second ratCode ratCode).comp params
  let retained := (Procedure.first (listCode ratCode) (listCode ratCode)).comp lists
  let selected := (Procedure.second (listCode ratCode) (listCode ratCode)).comp lists
  let b := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair
      ((sumMapProgram MediatorProgram.absoluteProgram).comp retained))).pair
      (MediatorProgram.absoluteProgram.comp c))
  let a := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 3).pair
    ((sumMapProgram linearProgram).comp selected))
  let d := Procedure.ratAdd.comp (b.pair
    (Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 4).pair
      ((sumMapProgram squareProgram).comp selected))))
  exact QuantumRoutingCode.scaleProgram.comp (a.pair (d.pair n))

def actualInput (G : QMARationalExchangeGraph) (s : Finset G.Edge) (N : ℚ) {r : ℕ}
    (retained : {e // e ∉ s} ≃ Fin r) : Input :=
  ((N,G.constant),(List.ofFn (fun i => G.weight (retained.symm i).val),
    List.ofFn (fun i => G.weight (qmaSelectedIndex s i))))

theorem value_actual (G : QMARationalExchangeGraph) (s : Finset G.Edge) (N : ℚ) {r : ℕ}
    (retained : {e // e ∉ s} ≃ Fin r) :
    value (actualInput G s N retained) = G.pathScale s N := by
  simp only [value,base,active,correction,actualInput,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,linearCost,squareCost,QMARationalExchangeGraph.pathScale]
  rw [retained.symm.sum_comp (fun e => |G.weight e.val|)]

end ContinuumCoulomb.QuantumPathScaleProgram

end

end OAI
