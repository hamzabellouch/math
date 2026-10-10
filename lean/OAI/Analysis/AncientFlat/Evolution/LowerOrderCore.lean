import OAI.Analysis.AncientFlat.Evolution.InitialCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior ParabolicInitial
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

abbrev Coefficients (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  (j : Fin 3) → V × ℝ → (V [×(j.val+1)]→L[ℝ] ℂ) →L[ℝ] ℂ
def spatialLower (c : Coefficients V) (u : ℝ → V → ℂ) (p : V × ℝ) : ℂ :=
  ∑ j : Fin 3, c j p (iteratedFDeriv ℝ (j.val+1) (u p.2) p.1)
end ParabolicLowerOrder

end

end OAI
