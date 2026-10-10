import OAI.Geometry.Relativity.CKS.ConstructedOuterMetric

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def flowEnergy (p : E) (t : ℝ) : ℝ := Real.sqrt (1+t^2*‖p‖^2)
def flowCoeff (p : E) (t : ℝ) : ℝ := t^2/(flowEnergy p t+1)
def flowD (p : E) (t : ℝ) (n : E) : ℝ := flowEnergy p t+t*inner ℝ p n
def flowS (p : E) (t : ℝ) (n : E) : E := n+(t+flowCoeff p t*inner ℝ p n) • p
def flowPhi (p : E) (t : ℝ) (n : E) : E := (flowD p t n)⁻¹ • flowS p t n

def boostField (p n : E) : E := p-inner ℝ p n • n

def flowDLinear (p : E) (t : ℝ) : E →L[ℝ] ℝ := t • innerSL ℝ p
def flowSLinear (p : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (flowCoeff p t • innerSL ℝ p).smulRight p

lemma flowEnergy_pos (p : E) (t : ℝ) : 0 < flowEnergy p t := Real.sqrt_pos.2 (by positivity)
lemma flowEnergy_sq (p : E) (t : ℝ) : flowEnergy p t ^2 = 1+t^2*‖p‖^2 := Real.sq_sqrt (by positivity)
lemma flowEnergy_add_pos (p : E) (t : ℝ) : 0 < flowEnergy p t+1 := by linarith [flowEnergy_pos p t]
lemma flowEnergy_gt (p : E) (t : ℝ) : ‖t • p‖ < flowEnergy p t := by
  rw [norm_smul, Real.norm_eq_abs]
  have hs : (|t| * ‖p‖)^2 = t^2*‖p‖^2 := by rw [mul_pow, sq_abs]
  nlinarith [flowEnergy_sq p t, flowEnergy_pos p t, norm_nonneg p, abs_nonneg t]

lemma flowEnergy_smooth (p : E) : ContDiff ℝ ∞ (flowEnergy p) :=
  (contDiff_const.add ((contDiff_id.pow 2).mul contDiff_const)).sqrt (fun t => by positivity)
lemma flowCoeff_smooth (p : E) : ContDiff ℝ ∞ (flowCoeff p) :=
  (contDiff_id.pow 2).div ((flowEnergy_smooth p).add contDiff_const)
    (fun t => (flowEnergy_add_pos p t).ne')
lemma flowD_smooth (p : E) : ContDiff ℝ ∞ (fun z : ℝ × E => flowD p z.1 z.2) :=
  ((flowEnergy_smooth p).comp contDiff_fst).add
    (contDiff_fst.mul (ContDiff.inner ℝ contDiff_const contDiff_snd))
lemma flowS_smooth (p : E) : ContDiff ℝ ∞ (fun z : ℝ × E => flowS p z.1 z.2) :=
  contDiff_snd.add ((contDiff_fst.add (((flowCoeff_smooth p).comp contDiff_fst).mul
    (ContDiff.inner ℝ contDiff_const contDiff_snd))).smul contDiff_const)

lemma flowD_eq (p : E) (t : ℝ) (n : E) :
    flowD p t n = denominator (flowEnergy p t) 1 (t • p) n := by simp [flowD, denominator, inner_smul_left]
lemma flowS_eq (p : E) (t : ℝ) (n : E) :
    flowS p t n = boundarySpatial (flowEnergy p t) 1 (t • p) n := by
  simp only [flowS, flowCoeff, boundarySpatial, inner_smul_left, conj_trivial, one_div,
    inv_one, one_mul, smul_smul]
  congr 1
  ring_nf
lemma flowD_pos (p : E) (t : ℝ) (n : Sphere) : 0 < flowD p t n := by
  rw [flowD_eq]
  exact denominator_pos (flowEnergy_gt p t) zero_lt_one n
lemma flowS_norm (p : E) (t : ℝ) (n : Sphere) : ‖flowS p t n‖ = flowD p t n := by
  rw [flowS_eq, flowD_eq]
  apply boundarySpatial_norm (flowEnergy_gt p t) zero_lt_one
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [flowEnergy_sq p t]
lemma flowPhi_norm (p : E) (t : ℝ) (n : Sphere) : ‖flowPhi p t n‖ = 1 := by
  rw [flowPhi, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (flowD_pos p t n)), flowS_norm]
  exact inv_mul_cancel₀ (flowD_pos p t n).ne'

lemma flowEnergy_derivative (p : E) (t : ℝ) :
    HasDerivAt (flowEnergy p) (t*‖p‖^2/flowEnergy p t) t := by
  have h := (Real.hasDerivAt_sqrt (show 1+t^2*‖p‖^2 ≠ 0 by positivity)).comp t
    ((((hasDerivAt_id t).pow 2).mul_const (‖p‖^2)).const_add 1)
  convert! h using 1
  simp [flowEnergy]
  ring

lemma flowCoeff_derivative (p : E) (t : ℝ) :
    HasDerivAt (flowCoeff p) (t/flowEnergy p t) t := by
  have h := ((hasDerivAt_id t).pow 2).div
    ((flowEnergy_derivative p t).add_const 1) (flowEnergy_add_pos p t).ne'
  convert! h using 1
  have hq := flowEnergy_sq p t
  have hpos := (flowEnergy_pos p t).ne'
  have hadd := (flowEnergy_add_pos p t).ne'
  simp only [id_eq, Pi.pow_apply, pow_one, mul_one, Nat.cast_ofNat, Nat.reduceSub]
  field_simp
  nlinarith [congrArg (fun x : ℝ => t*x) hq]

lemma flowD_derivative (p : E) (t : ℝ) (n : E) :
    HasDerivAt (fun t => flowD p t n) (t*‖p‖^2/flowEnergy p t+inner ℝ p n) t := by
  convert! (flowEnergy_derivative p t).add ((hasDerivAt_id t).mul_const (inner ℝ p n)) using 1
  simp
lemma flowS_derivative (p : E) (t : ℝ) (n : E) :
    HasDerivAt (fun t => flowS p t n) ((1+t/flowEnergy p t*inner ℝ p n) • p) t := by
  convert! (((hasDerivAt_id t).add ((flowCoeff_derivative p t).mul_const (inner ℝ p n))).smul_const p).const_add n using 1

lemma flowD_fderivative (p : E) (t : ℝ) (n : E) :
    HasFDerivAt (flowD p t) (flowDLinear p t) n := by
  convert! (((innerSL ℝ p).hasFDerivAt.const_mul t).const_add (flowEnergy p t)) using 1
lemma flowS_fderivative (p : E) (t : ℝ) (n : E) :
    HasFDerivAt (flowS p t) (flowSLinear p t) n := by
  convert! (hasFDerivAt_id n).add
    ((((innerSL ℝ p).hasFDerivAt.const_mul (flowCoeff p t)).const_add t).smul_const p) using 1

lemma flowD_transport (p : E) (t : ℝ) (n : E) :
    flowEnergy p t * (t*‖p‖^2/flowEnergy p t + inner ℝ p n) =
      flowDLinear p t (boostField p n)+inner ℝ p n*flowD p t n := by
  simp only [flowDLinear, smul_apply, innerSL_apply_apply, smul_eq_mul,
    boostField, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, flowD]
  field_simp [(flowEnergy_pos p t).ne']
  ring

lemma flowS_transport (p : E) (t : ℝ) (n : E) :
    flowEnergy p t • ((1+t/flowEnergy p t*inner ℝ p n) • p) =
      flowSLinear p t (boostField p n)+inner ℝ p n • flowS p t n := by
  simp only [flowSLinear, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
    boostField, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, flowS, flowCoeff]
  have hq : t^2*‖p‖^2/(flowEnergy p t+1) = flowEnergy p t-1 := by
    apply (div_eq_iff (flowEnergy_add_pos p t).ne').2
    nlinarith [flowEnergy_sq p t]
  have hc : flowEnergy p t * (1+t/flowEnergy p t*inner ℝ p n) =
      1+t*inner ℝ p n+t^2/(flowEnergy p t+1)*‖p‖^2 := by
    rw [show t^2/(flowEnergy p t+1)*‖p‖^2 = t^2*‖p‖^2/(flowEnergy p t+1) by ring, hq]
    field_simp [(flowEnergy_pos p t).ne']
    ring
  rw [smul_smul, hc]
  module

end
end CKSLorentz

end

end OAI
