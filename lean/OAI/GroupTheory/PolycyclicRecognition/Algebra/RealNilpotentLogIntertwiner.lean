import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentLogIntertwiner
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Real-linear maps intertwine the canonical rational logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
local instance realLogRationalSource : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
local instance realLogRationalTarget : Module ℚ W := Module.compHom W (algebraMap ℚ ℝ)

def rationalEndRestriction (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Module.End ℝ V →+* Module.End ℚ V where
  toFun f := f.restrictScalars ℚ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem real_nilpotentLog_intertwiner (f : V →ₗ[ℝ] W)
    (A : Module.End ℝ V) (B : Module.End ℝ W)
    (hA : IsNilpotent A) (hB : IsNilpotent B)
    (h : ∀ x, f (A x) = B (f x)) (x : V) :
    f (nilpotentLog A x) = nilpotentLog B (f x) := by
  let rV := rationalEndRestriction V
  let rW := rationalEndRestriction W
  have hh := nilpotentLog_intertwiner (f.restrictScalars ℚ) (rV A) (rW B)
    (hA.map rV) (hB.map rW) h x
  rw [nilpotentLog_map rV A hA, nilpotentLog_map rW B hB] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
