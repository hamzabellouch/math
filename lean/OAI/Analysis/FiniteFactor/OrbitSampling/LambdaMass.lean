import OAI.Analysis.FiniteFactor.OrbitSampling.Cube
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSampling_triangle_mass :
    ((unitIntervalMeasure.prod unitIntervalMeasure)
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 < p.2}).toReal = 1/2 := by
  rw [← samplingTestedFirstDensity_triangular_mass (1/2) 1 _ _ measurableSet_Icc measurableSet_Icc]
  have he : samplingTestedFirstDensity true (1/2) 1 (Set.Icc 0 1) (Set.Icc 0 1) =ᵐ[unitIntervalMeasure]
      (fun s => 1-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    simpa only [ite_true] using samplingTestedFirstDensity_whole true (1/2) 1 s
      (by norm_num) (by norm_num) (by norm_num) hs
  rw [integral_congr_ae he,unitIntervalMeasure,restrict_Ico_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num [intervalIntegral.integral_const]

theorem sourceSamplingLambda_mass (I : Finset SourceCoordinate) :
    ((sourceSamplingLambda I) Set.univ).toReal = (1/2 : ℝ)^I.card := by
  have he : sourceSamplingLambda I sourceSamplingCube = sourceSamplingLambda I Set.univ :=
    measure_congr (by filter_upwards [sourceSamplingLambda_cube I] with p hp; exact propext (iff_true_intro hp))
  rw [← he,← sourceSamplingEmptyTest_rectangle,sourceSamplingLambda_rectangle,
    sourceSamplingLimitRectangleMass_formula]
  have hE (i : SourceCoordinate) : sourceSamplingRationalX sourceSamplingEmptyTest i = Set.Icc (0 : ℝ) 1 ∧
      sourceSamplingRationalY sourceSamplingEmptyTest i = Set.Icc (0 : ℝ) 1 := by
    simp [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,sourceSamplingEmptyTest]
  change (∏ i ∈ I ∪ ∅, _) = _
  rw [Finset.union_empty]
  calc
    _ = ∏ _i ∈ I, (1/2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [ite_eq_left hi,(hE i).1,(hE i).2]
      exact sourceSampling_triangle_mass
    _ = _ := by simp

theorem sourceSamplingLambda_mass_pos (I : Finset SourceCoordinate) :
    0 < ((sourceSamplingLambda I) Set.univ).toReal := by
  rw [sourceSamplingLambda_mass]
  positivity

end
end FiniteFactor

end OAI
