import OAI.Analysis.FiniteFactor.Sampling.Weights

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

def samplingTestedFirstWeight (b : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if s ∈ E ∧ Int.fract (s+t) ∈ G then samplingWeight b h α s t else 0

def samplingTestedFirstDensity (b : Bool) (h α : ℝ) (E G : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t, samplingTestedFirstWeight b h α E G s t ∂unitIntervalMeasure

theorem samplingTestedFirstWeight_measurable (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingTestedFirstWeight b h α E G p.1 p.2) := by
  unfold samplingTestedFirstWeight
  exact Measurable.ite ((hE.preimage measurable_fst).inter
    (hG.preimage (sourceFract_measurable.comp (measurable_fst.add measurable_snd))))
    (samplingWeight_measurable b h α) measurable_const

theorem samplingTestedFirstWeight_bounds (b : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ)
    (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingTestedFirstWeight b h α E G s t ∧
    samplingTestedFirstWeight b h α E G s t ≤ samplingWeight b h α s t := by
  have hn := (samplingWeight_bounds b h α s t hh hα).1
  unfold samplingTestedFirstWeight
  split_ifs <;> simp [hn]

theorem samplingWeight_integrable (b : Bool) (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (samplingWeight b h α s) unitIntervalMeasure := by
  apply (integrable_const (max 1 (1/(h*α)))).mono'
    ((samplingWeight_measurable b h α).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    change ‖samplingWeight b h α s t‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (samplingWeight_bounds b h α s t hh hα).1]
    exact (samplingWeight_bounds b h α s t hh hα).2)

theorem samplingTestedFirstDensity_measurable (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingTestedFirstDensity b h α E G) :=
  (samplingTestedFirstWeight_measurable b h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

/-- Tests decrease the exact first marginal, which is at most one. -/
theorem samplingTestedFirstDensity_bounds (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G)
    (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ samplingTestedFirstDensity b h α E G s ∧
    samplingTestedFirstDensity b h α E G s ≤ 1 := by
  have hm : Measurable (samplingTestedFirstWeight b h α E G s) := (samplingTestedFirstWeight_measurable b h α E G hE hG).comp
    (measurable_const.prodMk measurable_id)
  have hi := (samplingWeight_integrable b h α s hh hα).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTestedFirstWeight_bounds b h α E G s t hh hα).1]
      exact (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2))
  refine ⟨integral_nonneg (fun t => (samplingTestedFirstWeight_bounds b h α E G s t hh hα).1), ?_⟩
  calc
    _ ≤ ∫ t, samplingWeight b h α s t ∂unitIntervalMeasure :=
      integral_mono_ae hi (samplingWeight_integrable b h α s hh hα)
        (Eventually.of_forall (fun t => (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2))
    _ ≤ 1 := by
      rw [samplingWeight_first_integral b h α s hh hh1 hα hs]
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · split_ifs <;> norm_num
      · linarith [hs.1]

/-- The first tested marginal has quadratic moment at most one in both
triangular and diagonal coordinates, uniformly in the measurable tests. -/
theorem samplingTestedFirstDensity_square (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingTestedFirstDensity b h α E G s ^ 2 ∂unitIntervalMeasure) ≤ 1 := by
  have hb : ∀ᵐ s ∂unitIntervalMeasure, 0 ≤ samplingTestedFirstDensity b h α E G s ∧
      samplingTestedFirstDensity b h α E G s ≤ 1 :=
    (ae_restrict_mem measurableSet_Ico).mono (fun s hs =>
      samplingTestedFirstDensity_bounds b h α E G hh hh1 hα hE hG s hs)
  have hb2 := hb.mono (fun s hs => show samplingTestedFirstDensity b h α E G s ^ 2 ≤ 1 by nlinarith)
  have hi : Integrable (fun s => samplingTestedFirstDensity b h α E G s ^ 2) unitIntervalMeasure :=
    (integrable_const (1 : ℝ)).mono'
      ((samplingTestedFirstDensity_measurable b h α E G hE hG).pow_const 2).aestronglyMeasurable
      (hb2.mono (fun s hs => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (samplingTestedFirstDensity b h α E G s))]
        exact hs))
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) hb2

end
end FiniteFactor

end OAI
