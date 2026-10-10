import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialSource
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalInitial

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialStep

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialSource
open JointPopulation
open scoped BigOperators Classical

variable {F : Type*} [Field F] {K N : ℕ}
  (counts : Fin K → Shape → ℕ) (total : ∀ h, ∑ u, counts h u = N)

def toLots (w : JointCanonicalInitial.RawWords counts) : Words K N :=
  fun h i => w h ((finCongr (total h)).symm i)

def positionMap :
    LocalMap (groupedSource F K N) (JointCanonicalInitial.rawSource counts) where
  x := fun x s => if s = toLots counts total x then 1 else 0
  y := fun y s => if s = toLots counts total y then 1 else 0
  z := fun z s => if s = toLots counts total z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict, groupedSource_eq_lots]
    funext x y z
    change (∏ h : Fin K, ∏ i : Fin N, CWStrands.strand (F := F) (Fin 8)
      (x h ((finCongr (total h)).symm i))
      (y h ((finCongr (total h)).symm i))
      (z h ((finCongr (total h)).symm i))) =
      ∏ h : Fin K, ∏ i : Positions counts h, CWStrands.strand (F := F) (Fin 8)
        (x h i) (y h i) (z h i)
    apply Finset.prod_congr rfl
    intro h _
    apply Fintype.prod_equiv (finCongr (total h)).symm
    intro i
    rfl

def initialExecution :
    Execution (cwSource F K N) (JointCanonicalInitial.rawSource counts) :=
  (AllFieldInitialSource.initialExecution F K N).restrict _ (positionMap counts total)

@[simp] theorem initialExecution_copies :
    Fintype.card (initialExecution (F := F) counts total).Copies = 1 := rfl

def maskedInitialExecution :
    Execution (cwSource F K N) (JointCanonicalInitial.maskedSource counts) :=
  (initialExecution counts total).restrict _
    (LocalMap.delete (JointCanonicalInitial.rawSource counts)
      (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
      (JointCanonicalInitial.sideMask counts 2))

abbrev CoarseWord := Position counts → Fin 17

def ordinaryAssignments (hx hy hz : CoarseWord counts → Prop) :
    JointExtraction.Assignment (JointCanonicalInitial.RawWords counts)
      (JointCanonicalInitial.RawWords counts) (JointCanonicalInitial.RawWords counts)
      (JointCoarseHashing.Triple (Position counts)) :=
  JointCoarseAssignment.assignments (ambientSet counts (fun _ => 16)) (targetSet counts)
    hx hy hz (JointCanonicalInitial.coarseWord counts) (JointCanonicalInitial.coarseWord counts)
    (JointCanonicalInitial.coarseWord counts) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)

theorem ordinaryAssignments_coherent (hx hy hz : CoarseWord counts → Prop) :
    JointExtraction.Coherent (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) := by
  apply JointCoarseAssignment.assignments_coherent
  · exact JointCanonicalInitial.maskedSource_support counts
  · intro _ _ _ _ _ _ _
    trivial
  · intro _ _ _ _ _ _ _ _
    trivial

def initialCanonicalMap (e : Target counts) :
    LocalMap (JointCanonicalInitial.ideal (F := F) counts e)
      (JointCanonicalInitial.canonical counts) where
  x := JointCanonicalInitial.coordinateMatrix counts e
  y := JointCanonicalInitial.coordinateMatrix counts e
  z := JointCanonicalInitial.coordinateMatrix counts e
  coefficient := JointCanonicalInitial.ideal_restrict counts e

def canonicalize {I : Type} [Fintype I] (target : I → Target counts)
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)))) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) :=
  E.restrict _ (LocalMap.directSum _ _ (fun i => initialCanonicalMap counts (target i)))

@[simp] theorem canonicalize_copies {I : Type} [Fintype I] (target : I → Target counts)
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)))) :
    Fintype.card (canonicalize counts target E).Copies = Fintype.card E.Copies := rfl

def repairedInitialExecution {I : Type} [Fintype I]
    (hx hy hz : CoarseWord counts → Prop) (target : I → Target counts)
    (injective : Function.Injective target) (shifts : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy
      (JointCanonicalInitial.ideal (F := F) counts (target i))
      (JointExtraction.branch (JointCanonicalInitial.maskedSource counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))) shifts) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) :=
  canonicalize counts target
    ((maskedInitialExecution counts total).extractSelectedAndRepair
      (ordinaryAssignments counts hx hy hz) (ordinaryAssignments_coherent counts hx hy hz)
      (fun i => triple counts (target i)) ((triple_injective counts).comp injective)
      (fun i => JointCanonicalInitial.ideal counts (target i)) shifts repair)

@[simp] theorem repairedInitialExecution_copies {I : Type} [Fintype I]
    (hx hy hz : CoarseWord counts → Prop) (target : I → Target counts)
    (injective : Function.Injective target) (shifts : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy
      (JointCanonicalInitial.ideal (F := F) counts (target i))
      (JointExtraction.branch (JointCanonicalInitial.maskedSource counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))) shifts) :
    Fintype.card
      (repairedInitialExecution counts total hx hy hz target injective shifts repair).Copies =
      2 ^ (3 * shifts) := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles shifts × PUnit) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin,
    Fintype.card_punit]
  exact Nat.mul_one _

end MatrixMultiplication.AllFieldInitialStep

end

end OAI
