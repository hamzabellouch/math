import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CoarseAssignment
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.ExactRecovery

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointIdealBranches

open MatrixMultiplication.Foundation JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {F X Y Z A B C : Type*} [CommSemiring F]

def ideal (T : Tensor F X Y Z)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) : Tensor F X Y Z :=
  ExactRecovery.delete T (fun x => cx x = e.1 ∧ usefulX e x)
    (fun y => cy y = e.2.1 ∧ usefulY e y)
    (fun z => cz z = e.2.2 ∧ usefulZ e z)

theorem branch_eq_delete_ideal
    (T : Tensor F X Y Z) (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    let a := assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ
    branch T a e = ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e)
      (fun x => a.x x = some e) (fun y => a.y y = some e) (fun z => a.z z = some e) := by
  classical
  dsimp only
  funext x y z
  by_cases h :
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).x x = some e ∧
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).y y = some e ∧
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).z z = some e
  · have hX := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e x => cx x = e.1) usefulX x e h.1
    have hY := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY y e h.2.1
    have hZ := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ z e h.2.2
    simp [branch, ExactRecovery.delete, ideal, h, hX.2.1, hX.2.2.1,
      hY.2.1.1, hY.2.2.1, hZ.2.1.1, hZ.2.2.1]
  · simp [branch, ExactRecovery.delete, h]

theorem ideal_delete (T : Tensor F X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    ideal (ExactRecovery.delete T px py pz) cx cy cz usefulX usefulY usefulZ e =
      ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e) px py pz := by
  funext x y z
  simp only [ideal, ExactRecovery.delete]
  split_ifs <;> simp_all

theorem branch_masked_eq_delete_ideal
    (T : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    let a := assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ
    branch (ExactRecovery.delete T px py pz) a e =
      ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e)
        (fun x => a.x x = some e ∧ px x)
        (fun y => a.y y = some e ∧ py y)
        (fun z => a.z z = some e ∧ pz z) := by
  dsimp only
  rw [branch_eq_delete_ideal, ideal_delete]
  funext x y z
  simp only [ExactRecovery.delete]
  split_ifs <;> simp_all

theorem masked_source_restriction [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor F X Y Z) (a : Assignment X Y Z (Triple A B C))
    (hcoherent : Coherent T a) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) :
    Tensor.restrict (assignmentMatrix a.x) (assignmentMatrix a.y) (assignmentMatrix a.z)
      (ExactRecovery.delete T px py pz) =
      Tensor.directSum (branch (ExactRecovery.delete T px py pz) a) := by
  apply restrict_assignments_eq_directSum
  apply coherent_of_support_subset T _ a hcoherent
  intro x y z h ht
  exact h (by simp [ExactRecovery.delete, ht])

end MatrixMultiplication.JointIdealBranches

end

end OAI
