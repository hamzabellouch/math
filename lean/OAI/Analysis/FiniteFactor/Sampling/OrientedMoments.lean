import OAI.Analysis.FiniteFactor.Sampling.TestedSelfMoment
import OAI.Analysis.FiniteFactor.OrbitSampling.Moments

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Both source orientations and both coordinate types, with exact x/y tests. -/
def samplingOrientedWeight (second triangular : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if second then
    if Int.fract (s-t) ∈ E ∧ s ∈ G then samplingWeight triangular h α (Int.fract (s-t)) t else 0
  else samplingTestedFirstWeight triangular h α E G s t

def samplingOrientedDensity (second triangular : Bool) (h α : ℝ) (E G : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t, samplingOrientedWeight second triangular h α E G s t ∂unitIntervalMeasure

theorem samplingOrientedWeight_measurable (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingOrientedWeight r b h α E G p.1 p.2) := by
  cases r
  · exact samplingTestedFirstWeight_measurable b h α E G hE hG
  · unfold samplingOrientedWeight
    simp only [ite_true]
    exact Measurable.ite ((hE.preimage (sourceFract_measurable.comp
      (measurable_fst.sub measurable_snd))).inter (hG.preimage measurable_fst))
      ((samplingWeight_measurable b h α).comp
        ((sourceFract_measurable.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)) measurable_const

theorem samplingOrientedWeight_bounds (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hα : 0 < α) (s t : ℝ) :
    0 ≤ samplingOrientedWeight r b h α E G s t ∧
    samplingOrientedWeight r b h α E G s t ≤ max 1 (1/(h*α)) := by
  cases r
  · exact ⟨(samplingTestedFirstWeight_bounds b h α E G s t hh hα).1,
      (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2.trans
        (samplingWeight_bounds b h α s t hh hα).2⟩
  · unfold samplingOrientedWeight
    simp only [ite_true]
    split_ifs
    · exact samplingWeight_bounds b h α _ _ hh hα
    · exact ⟨le_rfl,(by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)⟩

theorem samplingOrientedWeight_triangular_bounds (r : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) :
    0 ≤ samplingOrientedWeight r true h α E G s t ∧
    samplingOrientedWeight r true h α E G s t ≤ 1 := by
  cases r <;> unfold samplingOrientedWeight samplingTestedFirstWeight samplingWeight <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> norm_num

theorem samplingOrientedDensity_measurable (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingOrientedDensity r b h α E G) :=
  (samplingOrientedWeight_measurable r b h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

/-- Both triangular orientations have tested marginal densities between zero and one. -/
theorem samplingOrientedDensity_triangular_bounds (r : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) (s : ℝ) :
    0 ≤ samplingOrientedDensity r true h α E G s ∧
    samplingOrientedDensity r true h α E G s ≤ 1 := by
  have hm : Measurable (samplingOrientedWeight r true h α E G s) :=
    (samplingOrientedWeight_measurable r true h α E G hE hG).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (samplingOrientedWeight r true h α E G s) unitIntervalMeasure :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingOrientedWeight_triangular_bounds r h α E G s t).1]
      exact (samplingOrientedWeight_triangular_bounds r h α E G s t).2))
  refine ⟨integral_nonneg (fun t => (samplingOrientedWeight_triangular_bounds r h α E G s t).1),?_⟩
  simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun t => (samplingOrientedWeight_triangular_bounds r h α E G s t).2))

theorem samplingOrientedDensity_triangular_square (r : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingOrientedDensity r true h α E G s ^ 2 ∂unitIntervalMeasure) ≤ 1 := by
  have hb := samplingOrientedDensity_triangular_bounds r h α E G hE hG
  have hi := sampling_square_integrable unitIntervalMeasure _ 1
    (samplingOrientedDensity_measurable r true h α E G hE hG) hb
  simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun s => show samplingOrientedDensity r true h α E G s ^ 2 ≤ 1 by
      nlinarith [(hb s).1,(hb s).2]))

theorem sourceSampling_oriented_moment (stage : ℕ) (r b : Bool) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ s ∂unitIntervalMeasure,
      0 ≤ samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ∧
      samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ≤ 2) ∧
    (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ^ 2
      ∂unitIntervalMeasure) ≤ 1+4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) := by
  have hp := sourceSampling_parameters stage
  have herr : (0 : ℝ) ≤ 4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) := by positivity
  cases r
  · have hb : ∀ᵐ s ∂unitIntervalMeasure,
        0 ≤ samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ∧
        samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ≤ 1 :=
      (ae_restrict_mem measurableSet_Ico).mono (fun s hs => samplingTestedFirstDensity_bounds b _ _ E G
        hp.1 hp.2.1 hp.2.2 hE hG s hs)
    refine ⟨hb.mono (fun s hs => ⟨hs.1,hs.2.trans (by norm_num)⟩),?_⟩
    exact (samplingTestedFirstDensity_square b _ _ E G hp.1 hp.2.1 hp.2.2 hE hG).trans (by linarith)
  · cases b
    · exact sourceSampling_tested_second_moment stage E G hE hG
    · refine ⟨Eventually.of_forall (fun s => ?_),?_⟩
      · have hb := samplingOrientedDensity_triangular_bounds true (sourceSamplingWidth stage)
          (sourceSamplingCutoff stage) E G hE hG s
        exact ⟨hb.1,hb.2.trans (by norm_num)⟩
      · exact (samplingOrientedDensity_triangular_square true _ _ E G hE hG).trans (by linarith)

end
end FiniteFactor

end OAI
