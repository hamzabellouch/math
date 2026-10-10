import OAI.Probability.ContinuumTransition.DensityUniform

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory Metric
noncomputable section
namespace ContinuumTemperature

lemma strengthened_smallness {t m : ℝ} (ht : 0 < t)
    (hm : 17576*kernelHeight*m ≤ t) :
    2197*t*kernelHeight*m/2 ≤ t^2/8 ∧
    t^2/16 ≤ t^2/8-2197*t*kernelHeight*m/2 := by
  have hh := mul_le_mul_of_nonneg_left hm ht.le
  constructor <;> nlinarith only [hh,sq_nonneg t]

lemma strengthened_gap {t m a : ℝ} (ht : 0 < t)
    (hm : 17576*kernelHeight*m ≤ t) (ha : 1024*a < t) :
    t*a/2 < (t^2/8-2197*t*kernelHeight*m/2)/64 := by
  have hh := (strengthened_smallness ht hm).2
  have hh' := mul_lt_mul_of_pos_left ha ht
  nlinarith only [hh,hh',sq_nonneg t]

lemma physical_transform_active_bound {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t)
    {x w : Parameter} (hβ : 1/4 ≤ x.1) (hβ' : x.1 ≤ 2) (hh : x.2 ≤ 10)
    (hw : w ∈ activeLifts (physicalPressure (physicalProfile t σ R) t) a
      (meanField (physicalPressure (physicalProfile t σ R) t) a) x) :
    0 ≤ w.2 ∧ w.2 ≤ 1048576 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hx : x ∈ pressureDomain := by change 0 < x.1; linarith
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hmono := fun β (hβ : 0 < β) => monotone_physicalPressure hφ ht hβ.le hst hcore
  have hd := active_density_nonneg hmono hx hw
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  have hnon : 0 ≤ meanField (physicalPressure (physicalProfile t σ R) t) a x :=
    le_trans (div_nonneg (canonicalPressure_nonneg hφ ht (le_of_lt hx) hst hcore) ht0.le)
      (meanField_ge_base hP hx)
  have he := active_canonical_eq (physical_partialConjugate hφ ht hst hcore) hmono hx hw
  have hH := physicalCanonical_quadratic_lower ht (le_of_lt hx) hσ hR hs hsmall hd
  have hc := mul_le_mul_of_nonneg_right (physical_coefficient_lower ht0 (le_of_lt hx) hm) (sq_nonneg w.2)
  exact ⟨hd,bounded_density_of_quadratic ht.le hβ hβ' hh hat.le hd hnon (by linarith only [hH,hc]) he⟩

lemma physical_transform_gain {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t)
    {x : Parameter} (hβ : 1/4 ≤ x.1) (hβ' : x.1 ≤ 2) (hh : x.2 ≤ 10) :
    meanField (physicalPressure (physicalProfile t σ R) t) a x ≤
      physicalPressure (physicalProfile t σ R) t x+1048576^2*a := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hx : x ∈ pressureDomain := by change 0 < x.1; linarith
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hmono := fun β (hβ : 0 < β) => monotone_physicalPressure hφ ht hβ.le hst hcore
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  obtain ⟨w,hw⟩ := activeLifts_nonempty ha (convexOn_physicalPressure hφ ht hst hcore) hP hx
    (physical_meanField_attained ht ha hσ hR hs hsmall hgap hx)
  have hd := (physical_transform_active_bound ht ha hσ hR hs hm hat hβ hβ' hh hw).2
  have he := active_pressure_gap (physical_partialConjugate hφ ht hst hcore) hmono
    (fun β hβ h => physicalPressure_isLUB hφ ht hβ.le hst hcore (h := h)) hx ha.le hw hd
  have hh' := mul_le_mul_of_nonneg_right hβ' ha.le
  nlinarith only [he,hh']

end ContinuumTemperature
end
end

end OAI
