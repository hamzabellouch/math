import OAI.Combinatorics.PolynomialVacuum.Geometry.HoneycombVertex
import OAI.Combinatorics.PolynomialVacuum.Cylinder.LocalTurn

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

def arrowTriple (a b c : ℤ) (j : Fin 3) : ℤ := if j=0 then a else if j=1 then b else c

def IceTriple (a b c : ℤ) : Prop :=
  (∀j,arrowTriple a b c j=0) ∨ ∃i o : Fin 3,i≠o ∧ ∀j,
    arrowTriple a b c j=(if j=o then 1 else 0)-(if j=i then 1 else 0)

instance (a b c : ℤ) : Decidable (IceTriple a b c) := by unfold IceTriple; infer_instance

theorem up_ice (h j y : Spin) :
    IceTriple (-charge j) (-charge h) (charge y) ↔ charge y=charge h+charge j := by
  cases h <;> cases j <;> cases y <;> decide

theorem down_ice (h l i : Spin) :
    IceTriple (charge l) (charge h) (-charge i) ↔ charge i=charge h+charge l := by
  cases h <;> cases l <;> cases i <;> decide

theorem up_cubic_turn (h j y : Spin) (hc : charge y=charge h+charge j) :
    cubicTurn (-charge j) (-charge h) (charge y)=upTurn h j := by
  cases h <;> cases j <;> cases y <;> norm_num [charge,cubicTurn,upTurn] at *

theorem down_cubic_turn (h l i : Spin) (hc : charge i=charge h+charge l) :
    cubicTurn (charge l) (charge h) (-charge i)=downTurn h l := by
  cases h <;> cases l <;> cases i <;> norm_num [charge,cubicTurn,downTurn] at *

def vertexOccupation (a b c : ℤ) : ℕ := if a=0 ∧ b=0 ∧ c=0 then 0 else 1

theorem up_occupation (h j y : Spin) (hc : charge y=charge h+charge j) :
    vertexOccupation (-charge j) (-charge h) (charge y)=occupied h j := by
  cases h <;> cases j <;> cases y <;> norm_num [charge,vertexOccupation,occupied] at *

theorem down_occupation (h l i : Spin) (hc : charge i=charge h+charge l) :
    vertexOccupation (charge l) (charge h) (-charge i)=occupied h l := by
  cases h <;> cases l <;> cases i <;> norm_num [charge,vertexOccupation,occupied] at *

@[simp] theorem anglePhase_add (a b : ℤ) : anglePhase (a+b)=anglePhase a*anglePhase b := by
  unfold anglePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem anglePhase_two (a : ℤ) : anglePhase (2*a)=loopTurnPhase a := by
  unfold anglePhase loopTurnPhase
  congr 1
  push_cast
  ring

theorem loop_phase_add (a b : ℤ) : loopTurnPhase (a+b)=loopTurnPhase a*loopTurnPhase b := by
  unfold loopTurnPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

noncomputable def arrowVertexWeight (a b c : ℤ) : ℂ :=
  if IceTriple a b c then xStar^vertexOccupation a b c*loopTurnPhase (cubicTurn a b c) else 0

 

theorem honeycombPiece_arrows (l y i j h : Spin) :
    honeycombPiece (l,y) (i,j) h=
      arrowVertexWeight (-charge j) (-charge h) (charge y) *
      arrowVertexWeight (charge l) (charge h) (-charge i) *
      anglePhase (5*(charge i-charge y)) := by
  unfold honeycombPiece arrowVertexWeight
  simp only [up_ice,down_ice]
  by_cases hu : charge y=charge h+charge j
  · by_cases hd : charge i=charge h+charge l
    · rw [ite_eq_left ⟨hu,hd⟩,ite_eq_left hu,ite_eq_left hd,
        up_occupation h j y hu,down_occupation h l i hd,
        up_cubic_turn h j y hu,down_cubic_turn h l i hd]
      rw [pow_add,anglePhase_add,anglePhase_two,loop_phase_add]
      ring
    · simp [hu,hd]
  · simp [hu]

end PolynomialVacuumAlgebra

end OAI
