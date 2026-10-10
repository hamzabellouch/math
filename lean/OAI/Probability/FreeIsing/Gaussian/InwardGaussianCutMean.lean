import OAI.Probability.FreeIsing.Gaussian.InwardGaussianCutChannels
import OAI.Probability.FreeIsing.Trees.SelectedInwardPathAttenuation

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.InwardCutChannels
open PathSideBranches

theorem integral_inwardContinuationAverage_subset_le_exp_critical
    {d k : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (p : TreeShell d (k + 1)) (L : ℕ)
    (s : Finset ℕ) (hs : ∀ i ∈ s, k + 1 ≤ i ∧ i < k + 1 + L) :
    (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L s z
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1) * (s.card : ℝ)) := by
  let := hμ.isProbabilityMeasure
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    have h1 := Real.tanh_lt_one beta
    nlinarith
  apply integral_inwardContinuationAverage_le (by omega) μ t hθ p L s _
  intro w
  exact integral_cutInwardGaussianField_subset_attenuation_le_exp_critical
    hμ hbeta hd hcritical ht (appendCutContinuation p w).1 (k + 1) (by omega) s
    (by intro i hi; simpa only [(appendCutContinuation p w).2] using hs i hi)

theorem integral_inwardContinuationAverage_le_exp_critical
    {d k : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (p : TreeShell d (k + 1)) (L : ℕ) :
    (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L
      (Finset.Ico (k + 1) (k + 1 + L)) z
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1) * (L : ℝ)) := by
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using
    integral_inwardContinuationAverage_subset_le_exp_critical hμ hbeta hd hcritical ht p L
      (Finset.Ico (k + 1) (k + 1 + L)) (fun _ hi => Finset.mem_Ico.mp hi)

end Problem367.InwardCutChannels

end

end OAI
