import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussianTail
import OAI.NumberTheory.CubicMoment.Estimates.ThetaHeatKernelBound
import OAI.NumberTheory.CubicMoment.Estimates.NormSeries

namespace OAI

/-! A global quadratic decay bound for the nonzero Gaussian lattice tail. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGaussianPowerConstant : ℝ :=
  2*∑' a : {a : Eisenstein // a≠0},(norm a.val)^(-2:ℝ)

lemma cubicThetaGaussianPowerConstant_nonneg : 0≤cubicThetaGaussianPowerConstant := by
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))

lemma cubicThetaLatticeGaussianTail_power_bound {t : ℝ} (ht : 0<t) :
    cubicThetaLatticeGaussianTail t≤cubicThetaGaussianPowerConstant/t^2 := by
  have hs : Summable (fun a : {a : Eisenstein // a≠0} => (norm a.val)^(-2:ℝ)) := by
    have h := (summable_eisenstein_norm_rpow (s:=2) (by norm_num)).subtype
      (fun a : Eisenstein => a≠0)
    exact h
  have hm := hs.mul_left (2/t^2)
  have he : ∀ a : {a : Eisenstein // a≠0},
      Real.exp (-t*norm a.val)≤(2/t^2)*(norm a.val)^(-2:ℝ) := by
    intro a
    have hn := norm_pos_of_ne_zero a.property
    have h := power_exp_bound ht 2 (norm a.val) hn.le
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,
      Nat.cast_ofNat,mul_one] at h
    rw [Real.rpow_neg hn.le,Real.rpow_ofNat,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith [h]
  have h := (cubicThetaLatticeGaussianTail_summable ht).tsum_le_tsum he hm
  rw [tsum_mul_left] at h
  exact h.trans_eq (by unfold cubicThetaGaussianPowerConstant; ring)

lemma cubicThetaLatticeGaussianTail_div_bound {c t : ℝ} (hc : 0<c) (ht : 0<t) :
    cubicThetaLatticeGaussianTail (c/t)≤(cubicThetaGaussianPowerConstant/c^2)*t^2 := by
  apply (cubicThetaLatticeGaussianTail_power_bound (div_pos hc ht)).trans_eq
  field_simp

end CubicFirstMoment

end

end OAI
