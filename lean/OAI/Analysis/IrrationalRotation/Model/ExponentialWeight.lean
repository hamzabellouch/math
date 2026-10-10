import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

namespace Invariant233

noncomputable def exponentialWeight {X : Type*} (x₀ : X) (g : X → ℝ) : X → ℝ := by
  classical
  exact Function.update (fun x => Real.exp (-g x)) x₀ 0

end Invariant233

end OAI
