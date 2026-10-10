import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootSwitchCurves
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitPaths

namespace OAI

/-! # The specified Cartan visit path

This definition retains the actual outward-switch-return construction,
so later sampling does not depend on an arbitrary choice of a path.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

def cartanSupportVisitPath (w₀ w₁ : W) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r b : ℝ) :
    Path (n * Exp h₀) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let v := (supportLegDirection T H eW w₀ w₁ : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  exact supportVisitPath (fun t => Exp (t • v))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i))
    (by simp [hExp.map_zero]) n (Exp h₀) r b

end PolycyclicRecognition

end

end OAI
