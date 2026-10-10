import OAI.Probability.ContinuumTransition.ActiveSupports

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma physicalCanonical_quadratic_lower {t β d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (hd : 0 ≤ d) :
    (β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)/t)*d^2-
      (β*t/2)*d-1/t ≤ physicalCanonical (physicalProfile t σ R) t β d := by
  have hh := canonicalDensity_lower_coercive ht hβ hσ hR hs hsmall hd
  have he := entropy_dual_bound 0 hd
  norm_num only [zero_mul,Real.exp_zero,zero_sub] at he
  apply (le_div_iff₀ (lt_trans zero_lt_one ht)).mpr
  have hne : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  field_simp [hne]
  nlinarith only [he,hh]

lemma physical_meanField_attained {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (hgap : t*a/2 < (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)
    {x : Parameter} (hx : x ∈ pressureDomain) :
    ∃ d, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  apply meanField_attained ha (continuousOn_physicalPressure hφ ht hst hcore) hP hx
    (fun h => physicalPressure_isLUB hφ ht (le_of_lt hx) hst hcore (h := h))
    (c := x.1*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)/t)
    (b := x.1*t/2) (k := 1/t)
  · apply (lt_div_iff₀ ht0).mpr
    have hh := mul_lt_mul_of_pos_left hgap hx
    nlinarith only [hh]
  · exact fun d hd => physicalCanonical_quadratic_lower ht (le_of_lt hx) hσ hR hs hsmall hd

end ContinuumTemperature
end
end

end OAI
