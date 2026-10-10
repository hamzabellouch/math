import OAI.Analysis.FreeEntropy.MatrixFisherLiminf

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem classicalEntropy_continuousOn (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    ContinuousOn (classicalEntropy μ) (Ioi 0) := by
  intro s hs
  exact (classicalEntropy_hasDeriv μ hK hμ hs).continuousAt.continuousWithinAt
 theorem classicalFisher_intervalIntegrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K a b : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (ha : 0<a) (hb : 0<b) :
    IntervalIntegrable (classicalFisher μ) volume a b := by
  have hmin : 0 < min a b := lt_min ha hb
  have hi : IntervalIntegrable (fun s => (1/2:ℝ)*classicalFisher μ s) volume a b :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      ((classicalEntropy_continuousOn μ hK hμ).mono (fun s hs => hmin.trans_le hs.1))
      (fun s hs => classicalEntropy_hasDeriv μ hK hμ (hmin.trans hs.1))
      (fun s hs => mul_nonneg (by norm_num) (classicalFisher_nonneg μ (hmin.trans hs.1)))
  simpa only [← mul_assoc,show (2:ℝ)*(1/2:ℝ)=1 by norm_num,one_mul] using hi.const_mul (2:ℝ)
 theorem classicalEntropy_flow (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K a b : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (ha : 0<a) (hb : 0<b) :
    classicalEntropy μ b-classicalEntropy μ a = (1/2:ℝ)*∫s in a..b,classicalFisher μ s := by
  have hmin : 0 < min a b := lt_min ha hb
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (hs : s∈uIcc a b) => classicalEntropy_hasDeriv μ hK hμ (hmin.trans_le hs.1))
    ((classicalFisher_intervalIntegrable μ hK hμ ha hb).const_mul (1/2:ℝ))
  simpa only [intervalIntegral.integral_const_mul] using he.symm
 theorem smoothedDensity_cond_le (S : Set (EuclideanSpace ℝ ι)) {s : ℝ} (hs : 0<s)
    (x : EuclideanSpace ℝ ι) : smoothedDensity (ProbabilityTheory.cond volume S) s x ≤ (volume S).toReal⁻¹ := by
  rw [smoothedDensity,ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  have hi : Integrable (fun y : EuclideanSpace ℝ ι => normalKernel s (x-y)) volume := (normalKernel_integrable (ι := ι) hs).comp_sub_left x
  have hle := integral_mono_measure (Measure.restrict_le_self (μ := (volume : Measure (EuclideanSpace ℝ ι))) (s := S))
    (ae_of_all _ (fun y => (normalKernel_pos s (x-y)).le)) hi
  rw [integral_sub_left_eq_self (μ := (volume : Measure (EuclideanSpace ℝ ι))),normalKernel_integral hs] at hle
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr ENNReal.toReal_nonneg)
 theorem classicalEntropy_cond_lower (S : Set (EuclideanSpace ℝ ι))
    (hS0 : volume S ≠ 0) (hSt : volume S ≠ ⊤) {K s : ℝ}
    (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂ProbabilityTheory.cond volume S,‖y‖ ≤ K) (hs : 0<s) :
    Real.log (volume S).toReal ≤ classicalEntropy (ProbabilityTheory.cond volume S) s := by
  let ν := ProbabilityTheory.cond (volume : Measure (EuclideanSpace ℝ ι)) S
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure_of_finite hS0 hSt
  have hl x : Real.log (smoothedDensity ν s x) ≤ -Real.log (volume S).toReal := by
    have hb : smoothedDensity ν s x ≤ (volume S).toReal⁻¹ := smoothedDensity_cond_le S hs x
    have hp := smoothedDensity_pos ν hs x
    simpa only [Real.log_inv] using Real.log_le_log hp hb
  have hint := smoothedEntropy_integrable ν hs hK hμ
  have hbound := (smoothedDensity_integrable ν hs).mul_const (-Real.log (volume S).toReal)
  have hh := integral_mono_ae hint hbound (ae_of_all _ (fun x =>
    mul_le_mul_of_nonneg_left (hl x) (smoothedDensity_pos ν hs x).le))
  rw [integral_mul_const,smoothedDensity_integral ν hs,one_mul] at hh
  change Real.log (volume S).toReal ≤ -(∫x,smoothedDensity ν s x*Real.log (smoothedDensity ν s x))
  linarith
 theorem classicalEntropy_cond_flow_lower (S : Set (EuclideanSpace ℝ ι))
    (hS0 : volume S ≠ 0) (hSt : volume S ≠ ⊤) {K a b : ℝ}
    (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂ProbabilityTheory.cond volume S,‖y‖ ≤ K) (ha : 0<a) (hb : 0<b) :
    Real.log (volume S).toReal+(1/2:ℝ)*∫s in a..b,classicalFisher (ProbabilityTheory.cond volume S) s ≤
      classicalEntropy (ProbabilityTheory.cond volume S) b := by
  let ν := ProbabilityTheory.cond (volume : Measure (EuclideanSpace ℝ ι)) S
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure_of_finite hS0 hSt
  have he := classicalEntropy_flow ν hK hμ ha hb
  have hl := classicalEntropy_cond_lower S hS0 hSt hK hμ ha
  linarith
end FiniteEntropySeparation

end

end OAI
