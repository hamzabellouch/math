import Mathlib
import OAI.Probability.SKSupport.Backward.Backward

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma measurable_spatial_deriv {F : ℝ → ℝ → ℝ}
    (hm : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hd : ∀ r, Differentiable ℝ (F r)) :
    Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  let h : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht : Tendsto h atTop (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,?_⟩
    exact Eventually.of_forall (fun n => by simp only [Set.mem_compl_iff,Set.mem_singleton_iff]; dsimp [h]; positivity)
  apply measurable_of_tendsto_metrizable
    (f := fun n (p : ℝ × ℝ) => (h n)⁻¹*(F p.1 (p.2+h n)-F p.1 p.2))
  · intro n
    exact measurable_const.mul ((hm.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hm)
  · apply tendsto_pi_nhds.mpr
    intro p
    simpa only [Function.comp_def,smul_eq_mul] using (hd p.1 p.2).hasDerivAt.tendsto_slope_zero.comp ht

lemma measurable_varianceHeat_family {F : ℝ → ℝ → ℝ} {V : ℝ → ℝ}
    (hm : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) (hV : Measurable V) :
    Measurable (fun p : ℝ × ℝ => varianceHeat (V p.1) (F p.1) p.2) := by
  have hj : Measurable (fun q : (ℝ × ℝ) × ℝ => F q.1.1 (q.1.2+Real.sqrt (V q.1.1)*q.2)) :=
    hm.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add (((hV.comp (measurable_fst.comp measurable_fst)).sqrt).mul measurable_snd)))
  exact hj.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_backward {f : ℝ → ℝ} (hf : Measurable f) (c b : ℝ) :
    Measurable (fun p : ℝ × ℝ => backward c b f p.1 p.2) := by
  unfold backward varianceLogHeat
  split_ifs with hc
  · exact measurable_varianceHeat_family (F := fun _ z => f z) (hf.comp measurable_snd) (measurable_const.sub measurable_id)
  · exact (measurable_varianceHeat_family (F := fun _ z => Real.exp (c*f z))
      ((measurable_const.mul (hf.comp measurable_snd)).exp) (measurable_const.sub measurable_id)).log.div_const c

lemma varianceHeat_abs_le {g : ℝ → ℝ} {A : ℝ} (hA : ∀ z, |g z| ≤ A) (t x : ℝ) :
    |varianceHeat t g x| ≤ A := by
  have hnn : 0 ≤ A := (abs_nonneg (g 0)).trans (hA 0)
  change ‖∫ y, g (x+Real.sqrt t*y) ∂gaussianReal 0 1‖ ≤ A
  have hh := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (f := fun y => g (x+Real.sqrt t*y)) (C := A)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hA (x+Real.sqrt t*y)))
  simpa using hh

lemma hasDerivAt_integral_varianceHeat {F : ℝ → ℝ → ℝ} {A B : ℝ≥0}
    (hm : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hf : ∀ r, BoundedSmooth (F r)) (hA : ∀ r z, |F r z| ≤ A)
    (hB : ∀ r z, |deriv (F r) z| ≤ B) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ r in a..b, varianceHeat (r-a) (F r) z)
      (∫ r in a..b, varianceHeat (r-a) (deriv (F r)) x) x := by
  have hm' := measurable_spatial_deriv hm (fun r => (hf r).smooth.differentiable (by simp))
  have hH := measurable_varianceHeat_family hm (measurable_id.sub_const a)
  have hH' := measurable_varianceHeat_family (F := fun r => deriv (F r)) hm' (measurable_id.sub_const a)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z r => varianceHeat (r-a) (F r) z)
    (F' := fun z r => varianceHeat (r-a) (deriv (F r)) z)
    (bound := fun _ => (B:ℝ)) (s := Set.univ) (Filter.univ_mem)
    (Eventually.of_forall (fun z => (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    ?_ ((hH'.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
    (intervalIntegrable_const) ?_).2
  · apply (intervalIntegrable_const (c := (A:ℝ))).mono_fun
      (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    filter_upwards [] with r
    simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg A.coe_nonneg] using varianceHeat_abs_le (hA r) (r-a) x
  · filter_upwards [] with r hr z hz
    simpa only [Real.norm_eq_abs] using varianceHeat_abs_le (hB r) (r-a) z
  · filter_upwards [] with r hr z hz
    exact hasDerivAt_scaled_space ((hf r).smooth.of_le (by simp))
      (ExponentialBound.of_bounded (hA r)) (ExponentialBound.of_bounded (hB r)) (Real.sqrt (r-a)) z

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
