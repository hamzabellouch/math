import OAI.NumberTheory.DukePrimeDegree.Geometry.RootOrderCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRootEmbeddings

namespace OAI

/-! # The root-order exchange in the actual quotient parametrizations -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

def nextGroupCast (q : InitialRootStep n) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ
      positiveRootGeneratedGroup (allPositiveRoots n \ insert q.root q.processed) :=
  Homeomorph.setCongr (by rw [remaining,initialRemaining_erase])

@[simp] lemma nextGroupCast_val (q : InitialRootStep n)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    (q.nextGroupCast w).val = w.val := rfl

end InitialRootStep
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1))

def extendedRootParam
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) : X (d+1) :=
  (C.extend q.initial q.root q.mem_remaining q.least).quotientParam g
    (z.1.1,((z.1.2,z.2.2),q.nextGroupCast (q.nextConjugation d z.2.2 z.2.1)))

lemma extendedRootParam_eq_action
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    C.extendedRootParam q g z =
      rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2))
        (z.2.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2) := by
  rw [extendedRootParam,quotientParam_eq_action]
  change rightAction (Quotient.mk _ ((g*z.1.1.val)*
      (C.base z.1.2 * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2)))
        (q.nextConjugation d z.2.2 z.2.1).val = _
  have hb : (g*z.1.1.val)*(C.base z.1.2 * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2) =
      ((g*z.1.1.val)*C.base z.1.2) * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2 :=
    (mul_assoc _ _ _).symm
  rw [hb]
  change rightAction
      (rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2))
        (Matrix.SpecialLinearGroup.transvection q.distinct z.2.2))
      (q.nextConjugation d z.2.2 z.2.1).val = _
  rw [rightAction_mul]
  have he := q.rootOrderCoordinates_param d z.2
  exact congrArg (rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2))) he

lemma rectangle_physicalParam_eq_extended (k : Fin (d+1))
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z =
      C.extendedRootParam q g (z.1.val,(z.2.1.val,z.2.2)) := by
  rw [C.rectangle_physicalParam q g k Q z,C.extendedRootParam_eq_action]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
