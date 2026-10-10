import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowDerivativeIntegral

namespace OAI

/-! # Differentiating translated compactly supported test functions -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

theorem hasDerivAt_integral_translated_test
    {G W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (headd : ∀ s t, e (s + t) = e s * e t)
    (φ : G → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (dφ : ℝ → G → ℝ) (hdφ : Continuous dφ.uncurry)
    (hderiv : ∀ t g, HasDerivAt (fun s => φ (g * e s)) (dφ t g) t)
    (f : G → W) (hf : Continuous f) :
    HasDerivAt (fun t => ∫ g, φ (g * e t) • f g ∂μ)
      (∫ g, dφ 0 g • f g ∂μ) 0 := by
  let K := (fun z : G × ℝ => z.1 * e (-z.2)) '' (tsupport φ ×ˢ Icc (-1 : ℝ) 1)
  have hK : IsCompact K := (hcφ.prod isCompact_Icc).image (by fun_prop)
  have hzero (g : G) (hg : g ∉ K) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      φ (g * e t) = 0 := by
    by_contra h
    apply hg
    refine ⟨(g * e t, t), ⟨subset_tsupport φ h, ht⟩, ?_⟩
    dsimp
    rw [mul_assoc, ← headd]
    simp [he0]
  have hd0 (g : G) (hg : g ∉ K) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      dφ t g = 0 := by
    apply (hderiv t g).unique
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact hzero g hg u ⟨hu.1.le, hu.2.le⟩
  obtain ⟨D, hD⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hdφ.continuousOn
  let bound : G → ℝ := K.indicator (fun g => D * ‖f g‖)
  have hbound : Integrable bound μ := by
    exact ((hf.norm.const_mul D).continuousOn.integrableOn_compact hK).integrable_indicator
      hK.measurableSet
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (g : G) => φ (g * e t) • f g)
    (F' := fun t g => dφ t g • f g)
    (bound := bound) (s := Ioo (-1 : ℝ) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    ?_ ?_ ?_ ?_ hbound ?_).2
  · exact Eventually.of_forall (fun t => ((hφ.comp (by fun_prop)).smul hf).aestronglyMeasurable)
  · simp only [he0, mul_one]
    have hc : Continuous (fun g : G => φ g • f g) := hφ.smul hf
    have hk : HasCompactSupport (fun g : G => φ g • f g) := hcφ.smul_right
    exact hc.integrable_of_hasCompactSupport hk
  · exact ((hdφ.comp (continuous_const.prodMk continuous_id)).smul hf).aestronglyMeasurable
  · filter_upwards with g t ht
    by_cases hg : g ∈ K
    · rw [norm_smul, show bound g = D * ‖f g‖ from indicator_of_mem hg _]
      exact mul_le_mul_of_nonneg_right (hD (t, g) ⟨⟨ht.1.le, ht.2.le⟩, hg⟩) (norm_nonneg _)
    · simp [hd0 g hg t ht, bound, indicator_of_notMem hg]
  · exact Eventually.of_forall (fun g t _ => (hderiv t g).smul_const (f g))

end PolycyclicRecognition

end

end OAI
