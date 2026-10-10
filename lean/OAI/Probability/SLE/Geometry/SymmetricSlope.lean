import OAI.Probability.SLE.Geometry.ReflectedRiemannSymmetry
import Mathlib.Analysis.Complex.RemovableSingularity

namespace OAI

/-! Reflection is preserved by the removable difference quotient at the
origin; consequently its Taylor coefficients there are real. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma derivative_real_of_reflection {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ))
    {f : ℂ → ℂ} (hs : ∀ z ∈ D, f (conj z)=conj (f z)) :
    conj (deriv f 0)=deriv f 0 := by
  have he : (conj ∘ f ∘ conj) =ᶠ[𝓝 (0:ℂ)] f := by
    filter_upwards [hD] with z hz
    simp only [Function.comp_apply,hs z hz,conj_conj]
  have hd := he.deriv_eq
  simpa only [deriv_conj_conj,Function.comp_apply,map_zero] using hd

lemma dslope_reflection {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ))
    {f : ℂ → ℂ} (hs : ∀ z ∈ D, f (conj z)=conj (f z)) :
    ∀ z ∈ D, dslope f 0 (conj z)=conj (dslope f 0 z) := by
  have hz : f 0=conj (f 0) := by simpa only [map_zero] using hs 0 (mem_of_mem_nhds hD)
  intro z hzm
  by_cases he : z=0
  · simpa only [he,map_zero,dslope_same] using (derivative_real_of_reflection hD hs).symm
  · have hec : conj z ≠ 0 := by
      intro hc
      apply he
      simpa only [conj_conj,map_zero] using congrArg conj hc
    simp only [dslope_of_ne _ he,dslope_of_ne _ hec,slope,vsub_eq_sub,sub_zero,
      smul_eq_mul,hs z hzm,map_mul,map_inv₀,map_sub,hz.symm]

lemma analyticAt_dslope_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (dslope f 0) 0 := by
  obtain ⟨r,hr,ha⟩ := hf.exists_ball_analyticOnNhd
  have hd := (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hr)).mpr
    ha.differentiableOn
  exact hd.analyticAt (ball_mem_nhds (0:ℂ) hr)

end SLEExactGauge

end

end OAI
