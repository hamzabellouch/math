import OAI.Analysis.FreeEntropy.GaussianFlow

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
def normalizedMatrixEntropy (μ : Measure (MatrixCoordinates n d)) (s : ℝ) : ℝ :=
  classicalEntropy μ (s/d)/(d:ℝ)^2+(n:ℝ)/2*Real.log d
 theorem normalizedMatrixEntropy_hasDeriv (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s) :
    HasDerivAt (normalizedMatrixEntropy μ) ((1/2:ℝ)*normalizedMatrixFisher μ s) s := by
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hsD : 0 < s/(d:ℝ) := div_pos hs (by exact_mod_cast hd)
  have hf := (((classicalEntropy_hasDeriv μ hK hμ hsD).comp s
    ((hasDerivAt_id s).div_const (d:ℝ))).div_const ((d:ℝ)^2)).add_const ((n:ℝ)/2*Real.log d)
  have he : (1/2:ℝ)*classicalFisher μ (s/d)*(1/(d:ℝ))/(d:ℝ)^2 =
      (1/2:ℝ)*normalizedMatrixFisher μ s := by
    unfold normalizedMatrixFisher
    field_simp
  rw [he] at hf
  exact hf
 theorem normalizedMatrixFisher_nonneg (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : 0≤normalizedMatrixFisher μ s :=
  div_nonneg (classicalFisher_nonneg μ (div_pos hs (by exact_mod_cast hd))) (by positivity)
 theorem normalizedMatrixEntropy_continuousOn (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) :
    ContinuousOn (normalizedMatrixEntropy μ) (Ioi 0) :=
  fun _ hs => (normalizedMatrixEntropy_hasDeriv hd μ hK hμ hs).continuousAt.continuousWithinAt
 theorem normalizedMatrixFisher_measurable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) :
    Measurable (fun s : Ioi (0:ℝ) => normalizedMatrixFisher μ s) := by
  have he (s : Ioi (0:ℝ)) : normalizedMatrixFisher μ s = 2*deriv (normalizedMatrixEntropy μ) s := by
    rw [(normalizedMatrixEntropy_hasDeriv hd μ hK hμ s.property).deriv]
    ring
  simp_rw [he]
  exact ((measurable_deriv (normalizedMatrixEntropy μ)).comp measurable_subtype_coe).const_mul 2
 theorem normalizedMatrixFisher_intervalIntegrable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K a b : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (ha : 0<a) (hb : 0<b) :
    IntervalIntegrable (normalizedMatrixFisher μ) volume a b := by
  have hmin : 0 < min a b := lt_min ha hb
  have hi : IntervalIntegrable (fun s => (1/2:ℝ)*normalizedMatrixFisher μ s) volume a b :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      ((normalizedMatrixEntropy_continuousOn hd μ hK hμ).mono (fun s hs => hmin.trans_le hs.1))
      (fun s hs => normalizedMatrixEntropy_hasDeriv hd μ hK hμ (hmin.trans hs.1))
      (fun s hs => mul_nonneg (by norm_num) (normalizedMatrixFisher_nonneg hd μ (hmin.trans hs.1)))
  simpa only [← mul_assoc,show (2:ℝ)*(1/2:ℝ)=1 by norm_num,one_mul] using hi.const_mul (2:ℝ)
 theorem normalizedMatrixEntropy_flow (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K a b : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (ha : 0<a) (hb : 0<b) :
    normalizedMatrixEntropy μ b-normalizedMatrixEntropy μ a = (1/2:ℝ)*∫s in a..b,normalizedMatrixFisher μ s := by
  have hmin : 0 < min a b := lt_min ha hb
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (hs : s∈uIcc a b) => normalizedMatrixEntropy_hasDeriv hd μ hK hμ (hmin.trans_le hs.1))
    ((normalizedMatrixFisher_intervalIntegrable hd μ hK hμ ha hb).const_mul (1/2:ℝ))
  simpa only [intervalIntegral.integral_const_mul] using hf.symm
 theorem normalizedMatrixEntropy_cond_lower (hd : 0<d) (S : Set (MatrixCoordinates n d))
    (hS0 : volume S≠0) (hSt : volume S≠⊤) {K s : ℝ} (hK : 0≤K)
    (hμ : ∀ᵐy ∂ProbabilityTheory.cond volume S,‖y‖≤K) (hs : 0<s) :
    (d:ℝ)^(-2:ℤ)*Real.log (volume S).toReal+(n:ℝ)/2*Real.log d ≤ normalizedMatrixEntropy (ProbabilityTheory.cond volume S) s := by
  have hi := classicalEntropy_cond_lower S hS0 hSt hK hμ (show 0 < s/(d:ℝ) from div_pos hs (by exact_mod_cast hd))
  simpa [normalizedMatrixEntropy,zpow_neg,div_eq_mul_inv,mul_comm] using
    add_le_add_right (div_le_div_of_nonneg_right hi (sq_nonneg (d:ℝ))) ((n:ℝ)/2*Real.log d)
end FiniteEntropySeparation

end

end OAI
