import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortRank
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalProgram

namespace OAI

/-! The sorted endpoint port is evaluated by counting incident edges whose
lane color is smaller. Each record contains the two endpoints and lane color. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Entry := ℕ × (ℕ × ℕ)
def entryCode : Entry → List Bool := prodCode Nat.bits pairCode

def below (vc : Pair) (e : Entry) : Bool :=
  decide ((e.1=vc.1 ∨ e.2.1=vc.1) ∧ e.2.2<vc.2)

abbrev Input := Pair × List Entry
def inputCode : Input → List Bool := prodCode pairCode (listCode entryCode)
def value (x : Input) : ℕ := (x.2.map (below x.1)).countP id

noncomputable def belowProgram : Procedure (prodCode pairCode entryCode)
    Procedure.boolCode (fun x => below x.1 x.2) := by
  let vc := Procedure.first pairCode entryCode
  let e := Procedure.second pairCode entryCode
  let v := (Procedure.first Nat.bits Nat.bits).comp vc
  let c := (Procedure.second Nat.bits Nat.bits).comp vc
  let left := (Procedure.first Nat.bits pairCode).comp e
  let rest := (Procedure.second Nat.bits pairCode).comp e
  let right := (Procedure.first Nat.bits Nat.bits).comp rest
  let lane := (Procedure.second Nat.bits Nat.bits).comp rest
  let incident := Procedure.boolOr.comp
    ((Procedure.binaryEq.comp (left.pair v)).pair (Procedure.binaryEq.comp (right.pair v)))
  let smaller := Procedure.binaryLe.comp
    ((Procedure.binaryAdd.comp (lane.pair (Procedure.constant _ Nat.bits 1))).pair c)
  exact (Procedure.boolAnd.comp (incident.pair smaller)).congrFun (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,below]
    omega)

noncomputable def program : Procedure inputCode unaryCode value :=
  QuantumOrdinalProgram.countProgram.comp
    (Procedure.listMapWith (f := below) (0,(0,0)) false belowProgram)

theorem count_ofFn {n : ℕ} (entries : Fin n → Entry) (vc : Pair) :
    value (vc,List.ofFn entries) =
      (Finset.univ.filter (fun i =>
        ((entries i).1=vc.1 ∨ (entries i).2.1=vc.1) ∧ (entries i).2.2<vc.2)).card := by
  unfold value below
  rw [List.ofFn_eq_map,List.map_map,List.countP_map]
  simp only [Function.comp_def,id_eq]
  symm
  simpa only [List.toFinset_finRange] using (List.nodup_finRange n).card_eq_countP
    (P := fun i => ((entries i).1=vc.1 ∨ (entries i).2.1=vc.1) ∧ (entries i).2.2<vc.2)

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
