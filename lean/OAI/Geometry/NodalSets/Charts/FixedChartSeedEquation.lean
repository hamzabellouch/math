import OAI.Geometry.NodalSets.Charts.FixedChartAmbientLaplacian
import OAI.Geometry.NodalSets.Spectral.SphericalSeedEigenfunction

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff
noncomputable section

theorem sphericalSeed_fixed_chart_round_eigenfunction (N : ℕ) (p : Base) (y : BaseModel) :
    -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (sphericalSeed N) p y =
      seedEigenvalue N * sphericalSeed N ((extChartAt (𝓡 4) p).symm y) := by
  change -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1)
    (fun x : Base ↦ ambientRealSeed N x) p y = _
  rw [fixed_chart_round_operator_ambient_restriction _ (ambientRealSeed_contDiff N),
    ambientRealSeed_laplacian,ambientRealSeed_radial]
  have hd := ambientRealSeed_second_radial N ((extChartAt (𝓡 4) p).symm y : SeedAmbient)
  rw [seed_second_eq_iterated _ (ambientRealSeed_contDiff N),iteratedFDeriv_two_apply] at hd
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hd
  rw [hd]
  simp only [Pi.zero_apply,sphericalSeed,seedEigenvalue]
  ring

end
end Yau.Target

end OAI
