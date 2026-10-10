import OAI.Probability.FreeIsing.Estimates.BoundedAverageConcentration
import OAI.Probability.FreeIsing.Gaussian.InwardGaussianCutMean
import OAI.Probability.FreeIsing.Gaussian.InwardProducts
import OAI.Probability.FreeIsing.Trees.CutLevelConcentration
import OAI.Probability.FreeIsing.Trees.InwardCutProducts

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PathSideBranches InwardCutChannels CutContinuationChannels

theorem cutContinuationProduct_gaussianInwardConeFactor_le_cut {d k L : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      cutContinuationProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) p w ≤
        Real.exp (4 * beta / (1 - Real.tanh beta)) *
          inwardContinuationProduct μ t (Real.tanh beta) p w
            (Finset.Ico (k + 1) (k + 1 + L)) z := by
  have h := inward_attenuation_prod_le_cut hμ hbeta t
    (appendCutContinuation p w).1 (k + 1) L (by
      rw [(appendCutContinuation p w).2])
  simpa only [cutContinuationProduct_gaussianInwardConeFactor,
    inwardContinuationProduct_Ico_eq_range] using h

theorem average_gaussianInwardConeFactor_le_cut_average {d k : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      (∑ v ∈ cutDescendants I L,
        rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
          ((cutDescendants I L).card : ℝ) ≤
      Real.exp (4 * beta / (1 - Real.tanh beta)) *
        ((∑ p ∈ I, inwardContinuationAverage μ t (Real.tanh beta) p L
          (Finset.Ico (k + 1) (k + 1 + L)) z) / (I.card : ℝ)) := by
  have hθ0 := tanh_nonneg_of_beta_nonneg hbeta
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hcut : ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      ∀ p : TreeShell d (k + 1), ∀ w : ReducedTail (cutLastColor p) L,
      cutContinuationProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) p w ≤
        Real.exp (4 * beta / (1 - Real.tanh beta)) *
          inwardContinuationProduct μ t (Real.tanh beta) p w
            (Finset.Ico (k + 1) (k + 1 + L)) z :=
    ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun w =>
      cutContinuationProduct_gaussianInwardConeFactor_le_cut hμ hbeta t p w))
  filter_upwards [hcut] with z hz
  refine (average_rootPathProduct_le_continuation_average
    (gaussianInwardConeFactor μ t (Real.tanh beta) z)
    (fun v => gaussianInwardConeFactor_mem_Icc μ t hθ z v) I L).trans ?_
  calc
    _ ≤ (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L,
        Real.exp (4 * beta / (1 - Real.tanh beta)) *
          inwardContinuationProduct μ t (Real.tanh beta) p w
            (Finset.Ico (k + 1) (k + 1 + L)) z) /
          (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun w _ => hz p w)
    _ = _ := by
      simp only [inwardContinuationAverage, card_reducedTail,
        ← Finset.mul_sum, mul_div_assoc]

theorem measure_gaussian_inward_path_average_ge_le {d k : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 2 ≤ d)
    (t : ℝ≥0) (I : Finset (TreeShell d (k + 1))) (hI : I.Nonempty) (L : ℕ)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ p ∈ I, (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L
      (Finset.Ico (k + 1) (k + 1 + L)) z
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤ τ / 4) :
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      {z | Real.exp (4 * beta / (1 - Real.tanh beta)) * τ ≤
        (∑ v ∈ cutDescendants I L,
          rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
            ((cutDescendants I L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  classical
  let := hμ.isProbabilityMeasure
  have hθ0 := tanh_nonneg_of_beta_nonneg hbeta
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  choose F hF hb heq using (fun p : TreeShell d (k + 1) =>
    exists_inwardContinuationAverage_channel hd μ t hθ p L
      (Finset.Ico (k + 1) (k + 1 + L)))
  have hmeanF (p : TreeShell d (k + 1)) (hp : p ∈ I) :
      (∫ z, F p (globalCone p.1 z)
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 t))) ≤ τ / 4 := by
    simpa only [heq, PlantedSymmetry.gaussianNoiseLaw] using hmean p hp
  have hcon := hμ.measure_cutLevel_average_ge_le
    (by linarith : -1 ≤ Real.tanh beta) hθ1.le (k + 1)
    (fun _ : TreeVertex d => gaussianReal 0 t) F hF hb I hI hτ hmeanF
  change (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    {z | τ ≤ (∑ p ∈ I, F p (globalCone p.1 z)) / (I.card : ℝ)} ≤ _ at hcon
  refine le_trans ?_ hcon
  apply measure_mono_ae
  filter_upwards [average_gaussianInwardConeFactor_le_cut_average hμ hbeta t I L]
    with z hz
  intro h
  simp only [heq] at hz
  exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp (h.trans hz)

theorem measure_gaussian_inward_restricted_path_average_ge_le_double_exp {d : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    (forbidden : Finset (Fin d)) (hforbidden : forbidden.card ≤ 1) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      {z | Real.exp (4 * beta / (1 - Real.tanh beta)) *
        Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut forbidden k) L,
          rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
            ((cutDescendants (avoidingTreeCut forbidden k) L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  have hθ0 : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hcritical
  have hθ1 := Real.tanh_lt_one beta
  have hc := (ComponentSignalAttenuation.lossCoefficient_pos hθ0 hθ1).le
  have hω : 0 ≤ min (Real.sqrt (t : ℝ)) 1 :=
    le_min (Real.sqrt_nonneg _) (by norm_num)
  have hmean (p : TreeShell d (k + 1)) :
      (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L
        (Finset.Ico (k + 1) (k + 1 + L)) z
        ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
          Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) / 4 := by
    refine (integral_inwardContinuationAverage_le_exp_critical
      hμ hbeta hd hcritical ht p L).trans ?_
    calc
      _ ≤ Real.exp (-ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          (min (Real.sqrt (t : ℝ)) 1 * ℓ) / 2) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left htail (mul_nonneg hc hω)
        nlinarith
      _ ≤ Real.exp (-η * (min (Real.sqrt (t : ℝ)) 1 * ℓ)) / 4 :=
        attenuation_le_quarter_threshold (mul_nonneg hω hℓ) hη hlength
      _ = _ := by ring_nf
  have hq : η * min (Real.sqrt (t : ℝ)) 1 ≤ Real.log ((d : ℝ) - 1) / 8 :=
    (mul_le_of_le_one_right hη0 (min_le_right _ _)).trans hηlog
  have hd2 : 2 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  exact (measure_gaussian_inward_path_average_ge_le hμ hbeta hd2 t
    (avoidingTreeCut forbidden k) (avoidingTreeCut_nonempty hd2 forbidden hforbidden k)
    L (Real.exp_pos _).le (fun p _ => hmean p)).trans
      (ENNReal.ofReal_le_ofReal (BoundedAverageConcentration.exponential_card_bound
        (by linarith) hℓ hq (rpow_le_card_avoidingTreeCut hd2 forbidden hforbidden k hlevel)))

end Problem367

end

end OAI
