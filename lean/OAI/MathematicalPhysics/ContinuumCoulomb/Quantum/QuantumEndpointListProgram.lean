import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedArmProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkSupport
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! The endpoint arm list is computed from its ordinal port, lane color and
coarse vertex. All three quantities are supplied by the explicit slot and
incident-rank programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev ArmInput := ℕ × ℕ
def armCode : ArmInput → List Bool := prodCode unaryCode unaryCode

def armList (x : ArmInput) : List Pair :=
  if x.1=0 then (List.range (QuantumBufferedArmProgram.length 0 x.2+1)).map
    (QuantumBufferedArmProgram.point 0 x.2)
  else if x.1=1 then (List.range (QuantumBufferedArmProgram.length 1 x.2+1)).map
    (QuantumBufferedArmProgram.point 1 x.2)
  else (List.range (QuantumBufferedArmProgram.length 2 x.2+1)).map
    (QuantumBufferedArmProgram.point 2 x.2)

theorem armList_fin (a : Fin 3) (color : ℕ) :
    armList (a.val,color) = (List.range (QuantumBufferedArmProgram.length a color+1)).map
      (QuantumBufferedArmProgram.point a color) := by
  fin_cases a <;> simp [armList]

noncomputable def armProgram : Procedure armCode (listCode pairCode) armList := by
  let a := Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)
  let color := Procedure.second unaryCode unaryCode
  let is (k : ℕ) := Procedure.binaryEq.comp (a.pair (Procedure.constant armCode Nat.bits k))
  let branch (k : Fin 3) := (QuantumBufferedArmProgram.listProgram k).comp color
  exact (Procedure.conditional (is 0) (branch 0)
    (Procedure.conditional (is 1) (branch 1) (branch 2))).congrFun (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq,armList,id_eq])

def translate (B : ℕ) (p z : Pair) : Pair := qmaBufferedCellPoint (9*B+3) p z

noncomputable def translateProgram (B : ℕ) : Procedure (prodCode pairCode pairCode) pairCode
    (fun x => translate B x.1 x.2) := by
  let p := Procedure.first pairCode pairCode
  let z := Procedure.second pairCode pairCode
  let coord (take : Procedure pairCode Nat.bits Prod.fst) :=
    Procedure.binaryAdd.comp
      ((Procedure.binaryMul.comp ((Procedure.constant _ Nat.bits (8*(9*B+3+6))).pair
        (take.comp p))).pair (take.comp z))
  let y := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.constant _ Nat.bits (8*(9*B+3+6))).pair
      ((Procedure.second Nat.bits Nat.bits).comp p))).pair
        ((Procedure.second Nat.bits Nat.bits).comp z))
  exact (coord (Procedure.first Nat.bits Nat.bits)).pair y

abbrev Input := Pair × ArmInput
def inputCode : Input → List Bool := prodCode pairCode armCode
def value (B : ℕ) (x : Input) : List Pair := (armList x.2).map (translate B x.1)

noncomputable def program (B : ℕ) : Procedure inputCode (listCode pairCode) (value B) :=
  (Procedure.listMapWith (f := translate B) (0,0) (0,0) (translateProgram B)).comp
    ((Procedure.first pairCode armCode).pair
      (armProgram.comp (Procedure.second pairCode armCode)))

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) (e : M.Incident v) :
    value B (M.routeVertex v,((M.endpointPorts hd v).assign e).val,(M.laneColor e.val).val) =
      M.endpointArmList hd v e := by
  unfold value
  rw [armList_fin,List.map_map]
  rw [← M.endpointColors_assigned hd v e]
  simp only [QMASpatialExchangeModel.endpointArmList,QMASpatialExchangeModel.endpointArmLength,
    QuantumBufferedArmProgram.length_eq,translate,Function.comp_def]
  rfl

end ContinuumCoulomb.QuantumEndpointListProgram

end

end OAI
