import OAI.Geometry.NodalSets.Charts.SphereAmbientLaplacian
import OAI.Geometry.NodalSets.Elliptic.SeedAmbientHarmonic
import OAI.Geometry.NodalSets.Elliptic.SeedConcretePoint
import OAI.Geometry.NodalSets.Elliptic.SeedRadialDerivatives

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff
noncomputable section

lemma sphericalSeed_round_eigenfunction (N : ℕ) (p : Base) :
    -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (sphericalSeed N) p
      (extChartAt (𝓡 4) p p) = seedEigenvalue N * sphericalSeed N p := by
  change -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1)
    (fun x : Base ↦ ambientRealSeed N x) p _ = _
  rw [round_operator_ambient_restriction _ (ambientRealSeed_contDiff N),ambientRealSeed_laplacian,
    ambientRealSeed_radial]
  have hd := ambientRealSeed_second_radial N (p : SeedAmbient)
  rw [seed_second_eq_iterated _ (ambientRealSeed_contDiff N),iteratedFDeriv_two_apply] at hd
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hd
  rw [hd]
  simp only [Pi.zero_apply,sphericalSeed,seedEigenvalue]
  ring

theorem sphericalSeed_round_package (N : ℕ) (hN : 0 < N) :
    0 < seedEigenvalue N ∧ sphericalSeed N ≠ 0 ∧
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (sphericalSeed N) ∧
    ∀ p : Base, -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (sphericalSeed N) p
      (extChartAt (𝓡 4) p p) = seedEigenvalue N * sphericalSeed N p :=
  ⟨seedEigenvalue_pos hN,sphericalSeed_nonzero N,sphericalSeed_smooth N,
    sphericalSeed_round_eigenfunction N⟩

end
end Yau.Target

end OAI
