import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialStep
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AssignmentLoss

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialExact

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialStep
open JointPopulation JointCoarseAssignment JointExtraction JointAssignmentLoss
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

private def assignedDeletion {F X Y Z A B C : Type*} [CommSemiring F]
    (T : Tensor F X Y Z) (a : Assignment X Y Z (Triple A B C)) (e : Triple A B C)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) : Tensor F X Y Z :=
  ExactRecovery.delete T (fun x => a.x x = some e ∧ px x)
    (fun y => a.y y = some e ∧ py y) (fun z => a.z z = some e ∧ pz z)

private theorem assignedDeletion_eq_self_of_support {F X Y Z A B C : Type*}
    [CommSemiring F] (T : Tensor F X Y Z)
    (a : Assignment X Y Z (Triple A B C)) (e : Triple A B C)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (support : ∀ x y z, T x y z ≠ 0 →
      (a.x x = some e ∧ px x) ∧ (a.y y = some e ∧ py y) ∧ (a.z z = some e ∧ pz z)) :
    assignedDeletion T a e px py pz = T := by
  funext x y z
  unfold assignedDeletion ExactRecovery.delete
  by_cases ht : T x y z = 0
  · simp only [ht, ite_self]
  · exact ite_eq_left (support x y z ht)

variable {K N : ℕ}
  (counts : Fin K → Shape → ℕ)
  (hx hy hz : CoarseWord counts → Prop)

def Isolated (e : Target counts) : Prop :=
  survives hx hy hz (triple counts e) ∧
    ∀ f ∈ ambientSet counts (fun _ => 16), survives hx hy hz f →
      JointCoarseHashing.SharesSide (triple counts e) f → f = triple counts e

section Coefficients

variable {F : Type*} [CommRing F]

theorem assignments_on_ideal (e : Target counts)
    (ha : triple counts e ∈ ambientSet counts (fun _ => 16))
    (isolated : Isolated counts hx hy hz e)
    (x y z : JointCanonicalInitial.RawWords counts)
    (nonzero : JointCanonicalInitial.ideal (F := F) counts e x y z ≠ 0) :
    (ordinaryAssignments counts hx hy hz).x x = some (triple counts e) ∧
      (ordinaryAssignments counts hx hy hz).y y = some (triple counts e) ∧
      (ordinaryAssignments counts hx hy hz).z z = some (triple counts e) := by
  have hc : JointCanonicalInitial.coarseWord counts x = (triple counts e).1 ∧
      JointCanonicalInitial.coarseWord counts y = (triple counts e).2.1 ∧
      JointCanonicalInitial.coarseWord counts z = (triple counts e).2.2 := by
    by_contra hn
    simp [JointCanonicalInitial.ideal, JointIdealBranches.ideal, ExactRecovery.delete, hn]
      at nonzero
  have ht : triple counts e ∈ targetSet counts :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have he : triple counts e ∈ eligible (ambientSet counts (fun _ => 16))
      (targetSet counts) hx hy hz := by
    apply (mem_eligible_iff _ _ _ _ _ _).2
    exact ⟨ha, ht, isolated.1, fun f hf hs hfx => isolated.2 f hf hs (Or.inl hfx)⟩
  constructor
  · apply assignUseful_of_unique _ _ _ _ _ he hc.1 trivial
    intro f hf hfx
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inl (hfx.symm.trans hc.1))
  constructor
  · apply assignUseful_of_unique _ _ _ _ _ he ⟨hc.2.1, trivial⟩ trivial
    intro f hf hfy
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inr (Or.inl (hfy.1.symm.trans hc.2.1)))
  · apply assignUseful_of_unique _ _ _ _ _ he ⟨hc.2.2, trivial⟩ trivial
    intro f hf hfz
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inr (Or.inr (hfz.1.symm.trans hc.2.2)))

private theorem branch_eq_masked_ideal (e : Target counts) :
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts e) =
      assignedDeletion (JointCanonicalInitial.ideal counts e)
        (ordinaryAssignments counts hx hy hz) (triple counts e)
        (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
        (JointCanonicalInitial.sideMask counts 2) :=
  JointIdealBranches.branch_masked_eq_delete_ideal
    (JointCanonicalInitial.rawSource (F := F) counts)
    (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
    (JointCanonicalInitial.sideMask counts 2) (ambientSet counts (fun _ => 16)) (targetSet counts)
    hx hy hz (JointCanonicalInitial.coarseWord counts) (JointCanonicalInitial.coarseWord counts)
    (JointCanonicalInitial.coarseWord counts) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (triple counts e)

theorem branch_eq_ideal (e : Target counts)
    (ha : triple counts e ∈ ambientSet counts (fun _ => 16))
    (isolated : Isolated counts hx hy hz e) :
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts e) =
      JointCanonicalInitial.ideal counts e := by
  have hdelete : assignedDeletion (JointCanonicalInitial.ideal (F := F) counts e)
      (ordinaryAssignments counts hx hy hz) (triple counts e)
      (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
      (JointCanonicalInitial.sideMask counts 2) =
      JointCanonicalInitial.ideal counts e := by
    apply assignedDeletion_eq_self_of_support
    intro x y z hh
    have hm := JointCanonicalInitial.ideal_support_masks counts e x y z hh
    have ha := assignments_on_ideal counts hx hy hz e ha isolated x y z hh
    exact ⟨⟨ha.1, hm.1⟩, ⟨ha.2.1, hm.2.1⟩, ⟨ha.2.2, hm.2.2⟩⟩
  exact (branch_eq_masked_ideal counts hx hy hz e).trans hdelete

end Coefficients

section Execution

variable {F : Type*} [Field F]

def selectedExecution (total : ∀ h, ∑ u, counts h u = N)
    {I : Type} [Fintype I] (target : I → Target counts)
    (injective : Function.Injective target)
    (ambient : ∀ i, triple counts (target i) ∈ ambientSet counts (fun _ => 16))
    (isolated : ∀ i, Isolated counts hx hy hz (target i)) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) := by
  let input := maskedInitialExecution (F := F) counts total
  let extracted := input.restrict _
    (LocalMap.extract (JointCanonicalInitial.maskedSource counts)
      (ordinaryAssignments counts hx hy hz) (ordinaryAssignments_coherent counts hx hy hz))
  let selected := extracted.restrict _
    (LocalMap.selectBranches
      (branch (JointCanonicalInitial.maskedSource counts) (ordinaryAssignments counts hx hy hz))
      (fun i => triple counts (target i)) ((triple_injective counts).comp injective))
  have heq : Tensor.directSum (fun i => branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts (target i))) =
      Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)) := by
    apply congrArg Tensor.directSum
    funext i
    exact branch_eq_ideal counts hx hy hz (target i) (ambient i) (isolated i)
  let idMap := LocalMap.identity (Tensor.directSum (fun i =>
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts (target i))))
  let sameCoordinates : LocalMap
      (Tensor.directSum (fun i => branch (JointCanonicalInitial.maskedSource (F := F) counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))))
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i))) :=
    { x := idMap.x
      y := idMap.y
      z := idMap.z
      coefficient := idMap.coefficient.trans heq }
  exact AllFieldInitialStep.canonicalize counts target (selected.restrict _ sameCoordinates)

@[simp] theorem selectedExecution_copies (total : ∀ h, ∑ u, counts h u = N)
    {I : Type} [Fintype I] (target : I → Target counts)
    (injective : Function.Injective target)
    (ambient : ∀ i, triple counts (target i) ∈ ambientSet counts (fun _ => 16))
    (isolated : ∀ i, Isolated counts hx hy hz (target i)) :
    Fintype.card (selectedExecution (F := F) counts hx hy hz total target
      injective ambient isolated).Copies = 1 := rfl

end Execution

end MatrixMultiplication.AllFieldInitialExact

end

end OAI
