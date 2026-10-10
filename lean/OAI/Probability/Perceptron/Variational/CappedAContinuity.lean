import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma realTail_weak_tendsto (μ : ℕ→ProbabilityMeasure Time) (ν : ProbabilityMeasure Time)
    (hμ : Tendsto μ atTop (𝓝 ν)) (t : ℝ) :
    Tendsto (fun j=>realTail (μ j) t) atTop (𝓝 (realTail ν t)) := by
  let F : Time→ᵇℝ:=ContinuousMap.equivBoundedOfCompact Time ℝ ⟨fun s=>1-max t (s:ℝ),by fun_prop⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) F

lemma cappedDensity_bound (ν : Measure Time) {B : ℝ} (hB : B<1) (t : ℝ) :
    0≤cappedDensity ν B t ∧ cappedDensity ν B t≤(1-B)⁻¹^2 := by
  have hb : 0<1-B:=sub_pos.mpr hB
  have hm : 0 < max (1-B) (realTail ν t):=hb.trans_le (le_max_left _ _)
  refine ⟨sq_nonneg _,?_⟩
  exact pow_le_pow_left₀ (inv_nonneg.mpr hm.le)
    ((inv_le_inv₀ hm hb).mpr (le_max_left _ _)) 2

def cappedAError (μ ν : Measure Time) (B : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1,|cappedDensity μ B t-cappedDensity ν B t|

lemma cappedAError_nonneg (μ ν : Measure Time) (B : ℝ) : 0≤cappedAError μ ν B :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _=>abs_nonneg _)

lemma cappedA_sub_bound (μ ν : Measure Time) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hB : B<1) (r : Time) :
    |cappedA μ B r-cappedA ν B r|≤cappedAError μ ν B := by
  have hμ:=cappedDensity_continuous μ hB
  have hν:=cappedDensity_continuous ν hB
  rw [cappedA,cappedA,←intervalIntegral.integral_sub (hμ.intervalIntegrable _ _) (hν.intervalIntegrable _ _)]
  exact (intervalIntegral.abs_integral_le_integral_abs r.prop.1).trans
    (intervalIntegral.integral_mono_interval le_rfl r.prop.1 r.prop.2
      (ae_of_all _ fun _=>abs_nonneg _) ((hμ.sub hν).abs.intervalIntegrable _ _))

lemma cappedAError_tendsto (μ : ℕ→ProbabilityMeasure Time) (ν : ProbabilityMeasure Time)
    (hμ : Tendsto μ atTop (𝓝 ν)) {B : ℝ} (hB : B<1) :
    Tendsto (fun j=>cappedAError (μ j) ν B) atTop (𝓝 0) := by
  have hd (t : ℝ) : Tendsto (fun j=>cappedDensity (μ j) B t) atTop (𝓝 (cappedDensity ν B t)) := by
    exact ((tendsto_const_nhds.max (realTail_weak_tendsto μ ν hμ t)).inv₀
      (ne_of_gt ((sub_pos.mpr hB).trans_le (le_max_left _ _)))).pow 2
  have hh:=tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Ioc (0:ℝ) 1))
    (fun _ : ℝ=>2*(1-B)⁻¹^2)
    (F:=fun j t=>|cappedDensity (μ j) B t-cappedDensity ν B t|)
    (f:=fun _=>0)
    (fun j=>((cappedDensity_continuous (μ j) hB).sub (cappedDensity_continuous ν hB)).abs.measurable.aestronglyMeasurable)
    (integrable_const _) (fun j=>ae_of_all _ fun t=>by
      have h₁:=cappedDensity_bound (μ j) hB t
      have h₂:=cappedDensity_bound ν hB t
      rw [Real.norm_eq_abs,abs_abs]
      exact abs_le.mpr ⟨by linarith,by linarith⟩)
    (ae_of_all _ fun t=>by simpa using ((hd t).sub (tendsto_const_nhds (x:=cappedDensity ν B t))).abs)
  simpa only [cappedAError,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_zero] using hh
end SphericalPerceptronFreeEnergy

end

end OAI
