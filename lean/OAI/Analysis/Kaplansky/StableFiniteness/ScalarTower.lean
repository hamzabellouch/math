import OAI.Analysis.Kaplansky.Main

namespace OAI

noncomputable section

namespace Kaplansky.ComplexGrassmann

open Topology Set
open scoped Manifold ContDiff BigOperators
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)
instance productModelRealComplexTower : IsScalarTower ℝ ℂ (ProjectiveProductModel K) where
  smul_assoc r z f := by
    ext i x j
    exact smul_assoc r z (f i x j)


end Kaplansky.ComplexGrassmann

end

end OAI
