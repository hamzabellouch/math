import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A Schwartz function has a global Lipschitz bound from its first
derivative seminorm. This supplies domination in pointwise PV limits. -/
noncomputable section
open scoped NNReal
namespace SchwartzMap
open scoped _root_.SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def globalLipschitzConstant (f : SchwartzMap E ℂ) : ℝ≥0 :=
  ⟨SchwartzMap.seminorm ℝ 0 1 f, apply_nonneg _ _⟩

theorem global_lipschitz (f : SchwartzMap E ℂ) :
    LipschitzWith (_root_.OAI.SchwartzMap.globalLipschitzConstant f) f := by
  apply lipschitzWith_of_nnnorm_fderiv_le f.differentiable
  intro x
  change ‖fderiv ℝ f x‖≤SchwartzMap.seminorm ℝ 0 1 f
  rw [←norm_iteratedFDeriv_one]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f 1 x

end SchwartzMap

end

end OAI
