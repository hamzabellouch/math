import OAI.Probability.InvariantIsing.Spectral.PositiveResolventEigenbasis
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramTransformProbability

namespace OAI

/-! Identification of the physical matrix resolvent with the empirical spectral transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

def positiveResolventTest (t x : ℝ) : ℝ := 1/(t+max x 0)

lemma continuous_positiveResolventTest {t : ℝ} (ht : 0 < t) :
    Continuous (positiveResolventTest t) := by
  unfold positiveResolventTest
  apply continuous_const.div (continuous_const.add (continuous_id.max continuous_const))
  intro x
  exact ne_of_gt (add_pos_of_pos_of_nonneg ht (le_max_right x 0))

lemma positiveResolventTest_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ positiveResolventTest t x ∧ positiveResolventTest t x ≤ 1/t := by
  have hd : 0 < t+max x 0 := add_pos_of_pos_of_nonneg ht (le_max_right x 0)
  exact ⟨(one_div_pos.mpr hd).le,one_div_le_one_div_of_le ht (le_add_of_nonneg_right (le_max_right x 0))⟩

theorem gaussianGramStieltjes_empirical_integral {N m : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (∫ x, positiveResolventTest t x ∂(empiricalSpectralLaw hN (gaussianPatternEigenvalues z) : Measure ℝ)) =
      gaussianGramStieltjes t z := by
  rw [empiricalSpectralLaw_integral]
  have hB := gaussianPatternCoupling_posSemidef z
  have hs (i : Fin N) : positiveResolventTest t (gaussianPatternEigenvalues z i) =
      (t+hB.isHermitian.eigenvalues i)⁻¹ := by
    have hp : 0 ≤ gaussianPatternEigenvalues z i := by
      unfold gaussianPatternEigenvalues
      exact hB.eigenvalues_nonneg i
    unfold positiveResolventTest
    rw [max_eq_left hp]
    simp only [one_div,gaussianPatternEigenvalues]
  simp_rw [hs]
  rw [← positiveResolvent_trace_eigenvalues ht hB]
  change (1/(N : ℝ))*(gaussianGramResolvent t z).trace = (gaussianGramResolvent t z).trace/N
  ring

end InvariantIsing

end

end OAI
