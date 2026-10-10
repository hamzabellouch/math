import Mathlib

namespace OAI

namespace CliqueFreeLog

noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

end CliqueFreeLog

end OAI
