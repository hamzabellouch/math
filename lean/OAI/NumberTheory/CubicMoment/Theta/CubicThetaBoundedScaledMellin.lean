import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularUpperMellin

namespace OAI

/-! Entire upper Mellin tails at a positive scale, for the two bounded coefficient families in the actual projected transformation. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

def cubicThetaBoundedScaledAxis (a : Eisenstein→ℂ) (ℓ : ℤ) (z : ℂ) (r t : ℝ) : ℂ :=
  cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,r*t)

lemma cubicThetaBoundedScaledUpper_locallyIntegrable {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0<r) :
    LocallyIntegrable (thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r)) := by
  let g : ℝ→ℂ := fun t => cubicThetaNonconstant
    (cubicThetaAngularCoefficient a ℓ) (z,r*max (1/2) t)
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cubicThetaAngular_continuousAt hC
      ha ℓ (by positivity : 0<r*max (1/2) t)).comp
    fun_prop
  have he : thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r)=(Ioi 1).indicator g := by
    funext t
    by_cases ht : 1<t
    · simp only [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from ht),cubicThetaBoundedScaledAxis,g,
        max_eq_right (by linarith : (1/2:ℝ)≤t)]
    · simp only [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from ht)]
  rw [he]
  exact hg.locallyIntegrable.indicator measurableSet_Ioi

lemma cubicThetaBoundedScaledUpper_isBigO {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0<r) :
    thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi/18*r)*t)) := by
  apply IsBigO.of_bound (cubicThetaAngularExpConstant C ℓ)
  filter_upwards [eventually_ge_atTop (max 2 r⁻¹)] with t ht
  have ht1 : 1<t := by linarith [le_trans (le_max_left (2:ℝ) r⁻¹) ht]
  have hrt : 1≤r*t := by
    have hi : r⁻¹≤t := le_trans (le_max_right (2:ℝ) r⁻¹) ht
    have h := mul_le_mul_of_nonneg_left hi hr.le
    simpa only [mul_inv_cancel₀ hr.ne'] using h
  rw [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from ht1),cubicThetaBoundedScaledAxis,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc,neg_mul] using
    cubicThetaAngular_exponential_bound hC
      ha ℓ hrt z

lemma cubicThetaBoundedScaledUpper_small (a : Eisenstein→ℂ) (ℓ : ℤ) (z : ℂ) (r : ℝ) (s : ℂ) :
    thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r) =O[𝓝[>] 0]
      (fun t : ℝ => t^(-(s.re-1))) := by
  apply IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  rw [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr ht.le),norm_zero]
  simp

theorem cubicThetaBoundedScaledUpper_mellinConvergent {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ}
    (hr : 0<r) (s : ℂ) : MellinConvergent (thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r)) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (by positivity : 0<Real.pi/18*r)
    ((cubicThetaBoundedScaledUpper_locallyIntegrable hC ha ℓ z hr).locallyIntegrableOn _)
    (cubicThetaBoundedScaledUpper_isBigO hC ha ℓ z hr) (cubicThetaBoundedScaledUpper_small a ℓ z r s)
    (by linarith)

theorem cubicThetaBoundedScaledUpper_entire {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0<r) :
    Differentiable ℂ (mellin (thetaUpper (cubicThetaBoundedScaledAxis a ℓ z r))) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by positivity : 0<Real.pi/18*r)
    ((cubicThetaBoundedScaledUpper_locallyIntegrable hC ha ℓ z hr).locallyIntegrableOn _)
    (cubicThetaBoundedScaledUpper_isBigO hC ha ℓ z hr) (cubicThetaBoundedScaledUpper_small a ℓ z r s)
    (by linarith)

end CubicFirstMoment

end

end OAI
