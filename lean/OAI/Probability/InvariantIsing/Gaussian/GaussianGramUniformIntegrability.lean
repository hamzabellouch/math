import OAI.Probability.InvariantIsing.Gaussian.GaussianGramNormBound
import OAI.Probability.InvariantIsing.Gaussian.GaussianSingularSquareUI

namespace OAI

/-! The Davidson--Szarek uniform-integrability consequence for the physical Gram spectrum. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma uniformIntegrable_nat_mul_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : UniformIntegrable X 1 P) (n : ℕ) :
    UniformIntegrable (fun k ω => (n : ℝ)*X k ω) 1 P := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul] using
      (uniformIntegrable_const (ι := ℕ) le_rfl (by simp) (memLp_const (0 : ℝ)))
  | succ n ih =>
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using
        uniformIntegrable_add_real P _ _ ih hX

theorem gaussianPattern_spectralRadius_uniformIntegrable {α : ℝ} (hα : 0 ≤ α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) (c : ℝ) :
    UniformIntegrable (fun k ω => spectralRadius
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)) 1 P := by
  obtain ⟨n,hn⟩ := exists_nat_gt |c|
  let X (k : ℕ) (ω : Ω) := (gaussianPatternSingularMax (Z (k+1) ω))^2/(k+1)
  have hX : UniformIntegrable X 1 P := gaussianPatternSingularMax_square_uniformIntegrable hα P Z hZ
  refine uniformIntegrable_of_abs_le P _ _ ?_ (uniformIntegrable_nat_mul_real P X hX n) ?_
  · intro k
    have he : Measurable (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        spectralRadius (fun i => c*gaussianPatternEigenvalues z i)) := by
      apply measurable_spectralRadius
      exact Measurable.of_eval (fun i =>
        ((measurable_pi_apply i).comp
          (measurable_gaussianPatternEigenvalues (k+1) (gaussianPatternCount α (k+1)))).const_mul c)
    exact (he.aemeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable).aestronglyMeasurable
  intro k
  apply ae_of_all
  intro ω
  have hpos : 0 ≤ X k ω := div_nonneg (sq_nonneg _) (by positivity)
  have hr : 0 ≤ spectralRadius (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i) :=
    (abs_nonneg _).trans (abs_le_spectralRadius _ (0 : Fin (k+1)))
  rw [abs_of_nonneg hr,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hpos)]
  exact (gaussianPattern_spectralRadius_le c (Z (k+1) ω)).trans
    (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hn.le hpos)

end InvariantIsing

end

end OAI
