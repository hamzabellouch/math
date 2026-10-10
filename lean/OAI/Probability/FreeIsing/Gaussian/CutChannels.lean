import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorChannels
import OAI.Probability.FreeIsing.Trees.CutContinuationChannels
import OAI.Probability.FreeIsing.Trees.SelectedPathSegmentAttenuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PathSideBranches CutContinuationChannels

def gaussianConeFactor {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (theta : ℝ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) (v : TreeVertex d) : ℝ :=
  responseAttenuation theta (Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x)
    (Subtype.val : cone v → TreeVertex d) v z)) ^ 2

theorem gaussianConeFactor_mem_Icc {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z) (v : TreeVertex d) :
    gaussianConeFactor μ t theta z v ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gaussianConeFactor
  have hp := responseAttenuation_pos hθ (Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x)
    (Subtype.val : cone v → TreeVertex d) v z))
  have hl := responseAttenuation_le_one hθ (Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x)
    (Subtype.val : cone v → TreeVertex d) v z))
  exact ⟨sq_nonneg _, by nlinarith⟩

theorem exists_local_gaussianConeFactor {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) :
    ∃ F : ∀ v : TreeVertex d, ConeSample ℝ v → ℝ,
      (∀ v, Measurable (F v)) ∧ (∀ v z, 0 ≤ F v z ∧ F v z ≤ 1) ∧
      ∀ z v, globalFactors F z v = gaussianConeFactor μ t theta z v := by
  classical
  have hex (v : TreeVertex d) : ∃ f : ConeSample ℝ v → ℝ,
      Measurable f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, gaussianConeFactor μ t theta z v = f (globalCone v z) := by
    have hF : Measurable (Function.uncurry
        (fun s x => (t : ℝ) * spinSign s + x)) :=
      ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
        (t : ℝ)).add measurable_snd
    exact exists_selectedAttenuation_local_channel
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hF
      (Subtype.val : cone v → TreeVertex d) id v hθ
  choose f hf hb heq using hex
  exact ⟨f, hf, hb, fun z v => (heq v z).symm⟩

theorem cutContinuationProduct_gaussianConeFactor {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (z) :
    cutContinuationProduct (gaussianConeFactor μ t theta z) p w =
      ∏ i ∈ Finset.Ico (k + 1) (k + 1 + L),
        responseAttenuation theta
          (forwardGaussianField μ t (appendCutContinuation p w).1 i z) ^ 2 := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [gaussianConeFactor, forwardGaussianField, rootPathVertex,
    ConnectedHull.takeVertex, Nat.add_assoc]
  rfl

theorem integral_cutContinuationProduct_gaussianConeFactor_le {d k L : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    (∫ z, cutContinuationProduct (gaussianConeFactor μ t (Real.tanh beta) z) p w
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1) * (L : ℝ)) := by
  have h := integral_forwardGaussianField_subset_attenuation_le_exp_critical
    hμ hbeta hd hcritical ht (appendCutContinuation p w).1
      (Finset.Ico (k + 1) (k + 1 + L)) (by
        intro i hi
        rw [(appendCutContinuation p w).2]
        exact (Finset.mem_Ico.mp hi).2)
  simpa only [cutContinuationProduct_gaussianConeFactor, Nat.card_Ico,
    Nat.add_sub_cancel_left] using h

theorem measure_gaussian_restricted_path_average_ge_le_double_exp {d : ℕ}
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
      {z | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut forbidden k) L,
          rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) z) v.1) /
            ((cutDescendants (avoidingTreeCut forbidden k) L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  let := hμ.isProbabilityMeasure
  have hθ0 : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hcritical
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hc := (ComponentSignalAttenuation.lossCoefficient_pos hθ0 hθ1).le
  have hω : 0 ≤ min (Real.sqrt (t : ℝ)) 1 :=
    le_min (Real.sqrt_nonneg _) (by norm_num)
  obtain ⟨F, hF, hb, heq⟩ := exists_local_gaussianConeFactor μ t hθ
  have hfactor : globalFactors F = gaussianConeFactor μ t (Real.tanh beta) :=
    funext (fun z => funext (fun v => heq z v))
  have hmean (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
      (∫ z, cutContinuationProduct (globalFactors F z) p w
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 t))) ≤
          Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) / 4 := by
    rw [hfactor]
    change (∫ z, cutContinuationProduct (gaussianConeFactor μ t (Real.tanh beta) z) p w
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤ _
    refine (integral_cutContinuationProduct_gaussianConeFactor_le
      hμ hbeta hd hcritical ht p w).trans ?_
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
  have h := measure_restricted_path_average_ge_le_double_exp hμ
    (by linarith : -1 ≤ Real.tanh beta) hθ1.le (by omega : 2 ≤ d)
    (fun _ : TreeVertex d => gaussianReal 0 t) F hF hb forbidden hforbidden k L
    hℓ hq hlevel (fun p _ w => hmean p w)
  simpa only [hfactor, PlantedSymmetry.gaussianNoiseLaw] using h

end Problem367

end

end OAI
