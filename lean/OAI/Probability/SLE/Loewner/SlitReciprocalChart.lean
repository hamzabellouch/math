import OAI.Probability.SLE.Loewner.SlitHydrodynamicChart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace OAI

/-! In reciprocal coordinates the hydrodynamic chart is analytic across
infinity and has derivative one. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

def slitReciprocalMap (f : ℂ → ℂ) (a : ℝ) (w : ℂ) : ℂ :=
  w/(slitInfinityFactor f a w-deriv (slitInfinityFactor f a) 0*w)

@[simp] lemma slitReciprocalMap_zero (f : ℂ → ℂ) (a : ℝ) :
    slitReciprocalMap f a 0=0 := by simp [slitReciprocalMap]

lemma slitReciprocalMap_analyticAt {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f 0) (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ)) :
    AnalyticAt ℂ (slitReciprocalMap f a) 0 := by
  apply analyticAt_id.div
    ((slitInfinityFactor_analyticAt hf ha hd).sub (analyticAt_const.mul analyticAt_id))
  change slitInfinityFactor f a 0-deriv (slitInfinityFactor f a) 0*0 ≠ 0
  simp only [mul_zero,sub_zero,slitInfinityFactor_zero ha hd,ne_eq,one_ne_zero,not_false_eq_true]

lemma slitReciprocalMap_deriv {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f 0) (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ)) :
    deriv (slitReciprocalMap f a) 0=1 := by
  have hh := ((hasDerivAt_id (0:ℂ)).div
    (((slitInfinityFactor_analyticAt hf ha hd).differentiableAt.hasDerivAt).sub
      ((hasDerivAt_id (0:ℂ)).const_mul (deriv (slitInfinityFactor f a) 0))) (by
        change slitInfinityFactor f a 0-deriv (slitInfinityFactor f a) 0*0 ≠ 0
        simp only [mul_zero,sub_zero,slitInfinityFactor_zero ha hd,ne_eq,one_ne_zero,
          not_false_eq_true]))
  convert! hh.deriv using 1
  simp only [Pi.sub_apply,id_eq,mul_zero,sub_zero,
      slitInfinityFactor_zero ha hd,zero_mul,one_pow,div_one,one_mul]

lemma slitReciprocalMap_identity {f : ℂ → ℂ} (hf0 : f 0=0) (a : ℝ)
    {z : ℂ} (hz : z ≠ 0) :
    (slitReciprocalMap f a z⁻¹)⁻¹=slitHydrodynamicMap f a z := by
  rw [slitReciprocalMap,inv_div,div_eq_mul_inv,inv_inv,sub_mul,mul_comm _ z,
    slitInfinityFactor_identity hf0 a hz]
  simp only [slitHydrodynamicMap]
  rw [mul_assoc,inv_mul_cancel₀ hz,mul_one]

lemma slitReciprocalMap_reflection {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ))
    {f : ℂ → ℂ} (hs : ∀ z ∈ D, f (conj z)=conj (f z)) (a : ℝ) :
    ∀ z ∈ D, slitReciprocalMap f a (conj z)=conj (slitReciprocalMap f a z) := by
  have hH := slitInfinityFactor_reflection hD hs a
  have hd := derivative_real_of_reflection hD hH
  intro z hz
  simp only [slitReciprocalMap,hH z hz,map_div₀,map_sub,map_mul,hd]

theorem slitReciprocalMap_exists_local_inverse {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f 0) (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ)) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ r 0=0 ∧ deriv r 0=1 ∧
      (∀ᶠ z in 𝓝 (0:ℂ), r (slitReciprocalMap f a z)=z) ∧
      (∀ᶠ z in 𝓝 (0:ℂ), slitReciprocalMap f a (r z)=z) := by
  have hq := slitReciprocalMap_analyticAt hf ha hd
  have hqd := slitReciprocalMap_deriv hf ha hd
  have hn : deriv (slitReciprocalMap f a) 0 ≠ 0 := by rw [hqd]; exact one_ne_zero
  let r := hq.hasStrictDerivAt.localInverse _ _ _ hn
  have hr := hq.analyticAt_localInverse hn
  have hzero := (hq.hasStrictDerivAt.eventually_left_inverse hn).self_of_nhds
  have hrd := hq.hasStrictDerivAt.to_localInverse hn
  refine ⟨r,?_,?_,?_,?_,?_⟩
  · simpa only [slitReciprocalMap_zero] using hr
  · simpa only [slitReciprocalMap_zero] using hzero
  · simpa only [slitReciprocalMap_zero,hqd,inv_one] using hrd.hasDerivAt.deriv
  · exact hq.hasStrictDerivAt.eventually_left_inverse hn
  · simpa only [slitReciprocalMap_zero] using hq.hasStrictDerivAt.eventually_right_inverse hn

end SLEExactGauge

end

end OAI
