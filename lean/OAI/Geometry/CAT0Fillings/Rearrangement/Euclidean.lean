import Mathlib
import OAI.Geometry.CAT0Fillings.Rearrangement.Distribution
import OAI.Geometry.CAT0Fillings.Rearrangement.Inverse

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement

lemma lintegral_fun_norm_addHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f ‖x‖ ∂μ =
      (Module.finrank ℝ E : ℝ≥0∞)*μ (ball 0 1) *
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Module.finrank ℝ E-1))*f r := by
  let H := homeomorphUnitSphereProd E
  have hφ : Measurable (fun p : sphere (0:E) 1 × Ioi (0:ℝ) => f (p.2:ℝ)) :=
    hf.comp (measurable_subtype_coe.comp measurable_snd)
  calc
    _ = ∫⁻ x : ({(0:E)}ᶜ : Set E), f ‖x.1‖ ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x : E => f ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0:E) 1 × Ioi (0:ℝ), f (p.2:ℝ)
        ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)) := by
      rw [←μ.measurePreserving_homeomorphUnitSphereProd.map_eq,
        lintegral_map hφ H.continuous.measurable]
      simp only [H,homeomorphUnitSphereProd_apply_snd_coe]
    _ = μ.toSphere univ * ∫⁻ r : Ioi (0:ℝ), f r
        ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) := by
      rw [lintegral_prod _ hφ.aemeasurable]
      simp only [lintegral_const]
      rw [mul_comm]
    _ = _ := by
      rw [μ.toSphere_apply_univ,Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^(Module.finrank ℝ E-1))) by fun_prop)
          (show Measurable (fun r : Ioi (0:ℝ) => f r) from hf.comp measurable_subtype_coe)]
      congr 1
      exact lintegral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r^(Module.finrank ℝ E-1))*f r)

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (ν : Measure E) [ν.IsAddHaarMeasure]

noncomputable def euclideanRearrangement (μ : Measure ℝ) (U : ℝ) (x : E) : ℝ :=
  radialInverse (radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E)) U ‖x‖

lemma unitBall_real_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (ν : Measure E) [ν.IsAddHaarMeasure] : 0 < ν.real (ball (0:E) 1) := by
  exact ENNReal.toReal_pos_iff.mpr ⟨measure_ball_pos ν 0 (by norm_num), measure_ball_lt_top⟩

lemma rearrangement_lipschitz (μ : Measure ℝ) [IsFiniteMeasure μ] {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U →
      c*(t-s) ≤ radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) s -
        radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t) :
    LipschitzWith (Real.toNNReal c⁻¹) (euclideanRearrangement ν μ U) := by
  have hh := radialInverse_lipschitz hU hc
    ((radius_antitone μ (unitBall_real_pos ν).le).antitoneOn _) hD
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hh.dist_le_mul ‖x‖ ‖y‖).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using dist_norm_norm_le x y) (NNReal.coe_nonneg _))

lemma rearrangement_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (ν : Measure E) [ν.IsAddHaarMeasure] (μ : Measure ℝ) (U : ℝ) (x : E) :
    0 ≤ euclideanRearrangement ν μ U x := radialInverse_nonneg _ _ _

lemma rearrangement_compactSupport (μ : Measure ℝ) [IsFiniteMeasure μ] {U : ℝ}
    (hU : 0 ≤ U) : HasCompactSupport (euclideanRearrangement ν μ U) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0:E) (radiusDistribution μ (ν.real (ball 0 1))
      (Module.finrank ℝ E) 0))
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_contra hn
  apply hx
  exact radialInverse_zero_outside hU
    ((radius_antitone μ (unitBall_real_pos ν).le).antitoneOn _) (not_le.mp hn).le

lemma rearrangement_superlevel (μ : Measure ℝ) [IsFiniteMeasure μ] {U t : ℝ}
    (ht : 0 ≤ t) (htU : t < U) :
    {x : E | t < euclideanRearrangement ν μ U x} =
      ball 0 (radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t) := by
  have hn := Module.finrank_pos (R := ℝ) (M := E)
  ext x
  simpa only [mem_ofPred_eq,mem_ball,dist_zero_right,euclideanRearrangement] using
    radialInverse_superlevel ((radius_antitone μ (unitBall_real_pos ν).le).antitoneOn _) ht htU
      (radius_right_continuous μ (unitBall_real_pos ν) hn t)

lemma rearrangement_superlevel_mass (μ : Measure ℝ) [IsFiniteMeasure μ] {U : ℝ}
    (hU : 0 ≤ U) (hupper : μ (Ioi U) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ν {x | t < euclideanRearrangement ν μ U x} = μ (Ioi t) := by
  by_cases htU : t < U
  · rw [rearrangement_superlevel ν μ ht htU]
    have hω := unitBall_real_pos ν
    have hn := Module.finrank_pos (R := ℝ) (M := E)
    rw [ν.addHaar_ball _ (radius_nonneg μ hω.le t)]
    rw [←ofReal_measureReal (measure_ball_lt_top.ne),
      ←ENNReal.ofReal_mul (pow_nonneg (radius_nonneg μ hω.le t) _),mul_comm,
      radius_pow μ hω hn,ofReal_measureReal (measure_ne_top _ _)]
  · have he : {x | t < euclideanRearrangement ν μ U x} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt.mp htU).not_gt (hx.trans_le (radialInverse_le _ hU _))
    rw [he,measure_empty]
    exact (measure_mono_null (Ioi_subset_Ioi (not_lt.mp htU)) hupper).symm

theorem rearrangement_moments (μ : Measure ℝ) [IsFiniteMeasure μ] {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c) (hupper : μ (Ioi U) = 0)
    (hnegative : ∀ᵐ t ∂μ, 0 ≤ t)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U →
      c*(t-s) ≤ radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) s -
        radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t)
    {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ENNReal.ofReal ((euclideanRearrangement ν μ U x)^q) ∂ν =
      ∫⁻ t, ENNReal.ofReal (t^q) ∂μ := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (Eventually.of_forall (rearrangement_nonneg ν μ U))
    (rearrangement_lipschitz ν μ hU hc hD).continuous.measurable.aemeasurable hq,
    lintegral_rpow_eq_lintegral_meas_lt_mul μ hnegative measurable_id.aemeasurable hq]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [rearrangement_superlevel_mass ν μ hU hupper ht.le]
  rfl

end CAT0Fillings.Rearrangement
end

end OAI
