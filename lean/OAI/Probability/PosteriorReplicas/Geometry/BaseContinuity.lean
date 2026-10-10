import OAI.Probability.PosteriorReplicas.Geometry.FrameTubes

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma continuous_basePoint_label {d k : ℕ} (base : BaseLaw)
    (A : Rows d k) (x : Vec d) : Continuous (fun y => basePoint base A y x) := by
  cases base <;> unfold basePoint <;> fun_prop

lemma baseDensity_sphere_clipped {d k : ℕ} (hk : k + 2 < d) {A : Rows d k}
    (hA : LinearIndependent ℝ A) (y : Labels k) :
    baseDensity .spherical A y = ENNReal.ofReal
      (baseProjectionConstant .spherical d k *
        (max (1 - ‖liftLabel A y‖^2) 0) ^ (((d : ℝ) - k - 2) / 2) /
          Real.sqrt (rowGram A).det) := by
  have hβ : 0 < ((d : ℝ) - k - 2) / 2 := by
    have : (k : ℝ) + 2 < d := by exact_mod_cast hk
    linarith
  rw [baseDensity.eq_def, ite_eq_left hA]
  dsimp only [baseProjectionConstant]
  by_cases hy : ‖liftLabel A y‖ < 1
  · rw [ite_eq_left hy, max_eq_left (by nlinarith [norm_nonneg (liftLabel A y)])]
  · rw [ite_eq_right hy, max_eq_right (by nlinarith [le_of_not_gt hy]),
      Real.zero_rpow hβ.ne', mul_zero, zero_div, ENNReal.ofReal_zero]

lemma continuous_baseDensity {d k : ℕ} (hk : k + 2 < d) (base : BaseLaw)
    {A : Rows d k} (hA : LinearIndependent ℝ A) : Continuous (baseDensity base A) := by
  cases base
  · have hβ : 0 ≤ ((d : ℝ) - k - 2) / 2 := by
      have : (k : ℝ) + 2 < d := by exact_mod_cast hk
      linarith
    have he : baseDensity .spherical A = fun y => ENNReal.ofReal
        (baseProjectionConstant .spherical d k *
          (max (1 - ‖liftLabel A y‖^2) 0) ^ (((d : ℝ) - k - 2) / 2) /
            Real.sqrt (rowGram A).det) := funext (baseDensity_sphere_clipped hk hA)
    rw [he]
    apply ENNReal.continuous_ofReal.comp
    apply Continuous.div_const
    apply Continuous.const_mul
    exact (Real.continuous_rpow_const hβ).comp (by fun_prop)
  · have he : baseDensity .gaussian A = fun y => ENNReal.ofReal
        ((2 * Real.pi) ^ (-(k : ℝ) / 2) *
          Real.exp (-‖liftLabel A y‖^2 / 2) / Real.sqrt (rowGram A).det) := by
      funext y
      rw [baseDensity.eq_def, ite_eq_left hA]
    rw [he]
    exact ENNReal.continuous_ofReal.comp (by fun_prop)

lemma base_sample_representation {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) :
    ((volume.withDensity (baseDensity base A)).prod (stdGaussian (Vec d))).map
      (fun z => basePoint base A z.1 z.2) = base.measure d := by
  have : NeZero d := ⟨by omega⟩
  have hb0 := (measurable_baseDensity (d := d) (k := k) base).comp
    (show Measurable (fun y : Labels k => (A,y)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at hb0
  have hb : Measurable (baseDensity base A) := hb0
  have hm : Measurable (fun z : Labels k × Vec d => basePoint base A z.1 z.2) := by
    have h := (measurable_basePoint (d := d) (k := k) base).comp
      (show Measurable (fun z : Labels k × Vec d => ((A,z.1),z.2)) from
        (measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    exact h
  have : IsProbabilityMeasure (volume.withDensity (baseDensity base A)) := by
    rw [← projected_base_measure hA hk]
    infer_instance
  apply Measure.ext_of_lintegral
  intro g hg
  have hgm : Measurable (fun z : Labels k × Vec d => g (basePoint base A z.1 z.2)) := hg.comp hm
  rw [lintegral_map hg hm, lintegral_prod _ hgm.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hb (by fun_prop), base_lintegral hA hk base hg]
  apply lintegral_congr
  intro y
  simp only [Pi.mul_apply]
  rw [baseFiber_eq_map, lintegral_map hg (measurable_basePoint_fixed base A y)]

end PosteriorReplicas
end

end OAI
