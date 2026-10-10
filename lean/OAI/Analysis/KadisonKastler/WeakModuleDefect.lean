import OAI.Analysis.KadisonKastler.WeakRowAction
import OAI.Analysis.KadisonKastler.ProjectionModuleMaps

namespace OAI

/-! Right-module conditions are closed conditions in the bounded weak-map space. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weakModuleDefect {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) (a b : Algebra M) (ξ η : H) : ℂ :=
  boundedWeakAlgebraCoefficients F (a * b, ξ, η) -
    boundedWeakAlgebraCoefficients F (a, (b : H →L[ℂ] H) ξ, η)

theorem continuous_weakModuleDefect {M : VonNeumannAlgebra H} {c : ℝ}
    (a b : Algebra M) (ξ η : H) :
    Continuous (fun F : BoundedWeakAlgebraMap M c => weakModuleDefect F a b ξ η) := by
  have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
    continuous_induced_dom
  exact ((continuous_apply (a * b, ξ, η)).comp hcoeff).sub
    ((continuous_apply (a, (b : H →L[ℂ] H) ξ, η)).comp hcoeff)

theorem right_module_iff_weakModuleDefect_zero {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) :
    (∀ a b, F.map (a * b) = F.map a * b) ↔ ∀ a b ξ η, weakModuleDefect F a b ξ η = 0 := by
  constructor
  · intro h a b ξ η
    simp [weakModuleDefect, boundedWeakAlgebraCoefficients, h]
  · intro h a b
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    exact sub_eq_zero.mp (h a b ξ η)

theorem isClosed_right_module {M : VonNeumannAlgebra H} {c : ℝ} :
    IsClosed {F : BoundedWeakAlgebraMap M c | ∀ a b, F.map (a * b) = F.map a * b} := by
  have he : {F : BoundedWeakAlgebraMap M c | ∀ a b, F.map (a * b) = F.map a * b} =
      ⋂ a, ⋂ b, ⋂ ξ, ⋂ η, {F | weakModuleDefect F a b ξ η = 0} := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, right_module_iff_weakModuleDefect_zero]
  rw [he]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun ξ =>
    isClosed_iInter fun η => isClosed_eq (continuous_weakModuleDefect a b ξ η) continuous_const

end

end KadisonKastler

end OAI
