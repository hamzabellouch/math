import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternAspect
import OAI.Probability.InvariantIsing.Gaussian.GaussianCenteredSquare

namespace OAI

/-! Uniform integrability of the actual normalized squared Gaussian operator norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

theorem gaussianPatternSingularMax_square_uniformIntegrable {α : ℝ} (hα : 0 ≤ α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    UniformIntegrable (fun k ω => (gaussianPatternSingularMax (Z (k+1) ω))^2/(k+1)) 1 P := by
  let f (k : ℕ) := gaussianPatternSingularMax (N := k+1) (m := gaussianPatternCount α (k+1))
  let M (k : ℕ) := ∫ x, f k x ∂stdGaussian _
  let C (k : ℕ) (ω : Ω) := (f k (Z (k+1) ω)-M k)^2/(k+1)
  have hC : UniformIntegrable C 1 P := gaussianCenteredSquare_uniformIntegrable f
    (fun k => gaussianPatternSingularMax_lipschitz _ _) P (fun k => Z (k+1)) (fun k => hZ (k+1))
  let B : ℝ := 4+4*α
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdom : UniformIntegrable (fun k ω => B+(C k ω+C k ω)) 1 P :=
    uniformIntegrable_add_real P _ _
      (uniformIntegrable_const le_rfl (by simp) (memLp_const B))
      (uniformIntegrable_add_real P C C hC hC)
  refine uniformIntegrable_of_abs_le P _ _ ?_ hdom ?_
  · intro k
    exact (((hZ (k+1)).memLp_comp (finiteGaussian_lipschitz_memLp_two
      (gaussianPatternSingularMax_lipschitz _ _))).integrable_sq.div_const (k+1)).aestronglyMeasurable
  intro k
  apply ae_of_all
  intro ω
  have hd : (0 : ℝ) < k+1 := by positivity
  have hM : (M k)^2/(k+1) ≤ 2+2*α := gaussianPattern_mean_sq_div_le hα k
  have hC0 : 0 ≤ C k ω := div_nonneg (sq_nonneg _) hd.le
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le),abs_of_nonneg (by linarith : 0 ≤ B+(C k ω+C k ω))]
  change (f k (Z (k+1) ω))^2/(k+1) ≤ _
  have hs : (f k (Z (k+1) ω))^2/(k+1) ≤ 2*C k ω+2*(M k)^2/(k+1) := by
    dsimp [C]
    rw [← mul_div_assoc,← add_div]
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith [sq_nonneg (f k (Z (k+1) ω)-2*M k)]
  dsimp [B]
  rw [mul_div_assoc] at hs
  linarith

end InvariantIsing

end

end OAI
