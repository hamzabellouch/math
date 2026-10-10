import OAI.Probability.InvariantIsing.Gaussian.GaussianGramEdges
import OAI.Probability.InvariantIsing.Gaussian.MPMeasureSupport
import OAI.Probability.InvariantIsing.Pressure.InMeasurePerturbation

namespace OAI

/-! The proved Gaussian edge law also controls clipping to the nonnegative MP interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma mp_lower_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ marchenkoPasturLower α := by
  rw [marchenkoPasturLower_positive_part hα]
  exact sq_nonneg _

lemma mp_lower_le_upper {α : ℝ} (hα : 0 < α) :
    marchenkoPasturLower α ≤ marchenkoPasturB α :=
  (marchenkoPastur_support_bound hα (marchenkoPastur_left_mem hα)).2

theorem gaussianPattern_zero_upper_excess {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => spectralExcess (gaussianPatternEigenvalues (Z (k+1) ω))
      0 (marchenkoPasturB α)) atTop (fun _ => 0) := by
  have ht := gaussianPattern_spectralExcess_tendsto hα P Z hZ 1
  simp only [one_mul,min_eq_left (mp_lower_le_upper hα),max_eq_right (mp_lower_le_upper hα)] at ht
  apply tendstoInMeasure_zero_of_abs_le P _ _ ht
  intro k ω
  rw [abs_of_nonneg (spectralExcess_nonneg _ _ _),abs_of_nonneg (spectralExcess_nonneg _ _ _)]
  apply spectralExcess_le _ _ _ _ (spectralExcess_nonneg _ _ _)
  intro i
  have hb := spectralExcess_bounds (gaussianPatternEigenvalues (Z (k+1) ω))
    (marchenkoPasturLower α) (marchenkoPasturB α) i
  exact ⟨by linarith [mp_lower_nonneg hα.le],hb.2⟩

end InvariantIsing

end

end OAI
