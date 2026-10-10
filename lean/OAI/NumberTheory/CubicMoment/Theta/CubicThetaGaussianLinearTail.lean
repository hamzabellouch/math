import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussianPowerBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarGaussianReal

namespace OAI

/-! A uniform inverse-linear bound for the nonzero lattice heat sum.
It controls the nonzero first coordinate in the reduced cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaScalarGaussianReal_zero_tail {t : ℝ} (ht : 0<t) :
    cubicThetaScalarGaussianReal 0 (t/9)=1+cubicThetaLatticeGaussianTail t := by
  have hs : Summable (fun a : Eisenstein => Real.exp (-t*norm a)) := by
    convert cubicThetaScalarGaussianReal_summable 0 (div_pos ht (by norm_num : (0:ℝ)<9)) using 1
    funext a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    congr 1
    ring
  have he : cubicThetaScalarGaussianReal 0 (t/9)=
      ∑' a : Eisenstein,Real.exp (-t*norm a) := by
    apply tsum_congr
    intro a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    congr 1
    ring
  rw [he,hs.tsum_eq_add_tsum_ite 0]
  simp only [show norm (0:Eisenstein)=0 by simp [norm],mul_zero,Real.exp_zero]
  congr 1
  calc
    _ = ∑' a : Eisenstein,Set.indicator {a : Eisenstein | a≠0}
        (fun a => Real.exp (-t*norm a)) a := by
      apply tsum_congr
      intro a
      by_cases ha : a=0 <;> simp [ha,Set.indicator]
    _ = _ := (tsum_subtype {a : Eisenstein | a≠0} (fun a => Real.exp (-t*norm a))).symm

def cubicThetaGaussianLinearConstant : ℝ :=
  cubicThetaGaussianPowerConstant+(2*Real.pi/Real.sqrt 3)*
    (1+cubicThetaGaussianPowerConstant/(4*Real.pi^2/3)^2)

lemma cubicThetaGaussianLinearConstant_nonneg : 0≤cubicThetaGaussianLinearConstant := by
  unfold cubicThetaGaussianLinearConstant
  have h := cubicThetaGaussianPowerConstant_nonneg
  positivity

lemma cubicThetaLatticeGaussianTail_linear_bound {t : ℝ} (ht : 0<t) :
    cubicThetaLatticeGaussianTail t≤cubicThetaGaussianLinearConstant/t := by
  let D := cubicThetaGaussianPowerConstant
  let c := 4*Real.pi^2/3
  let A := (2*Real.pi/Real.sqrt 3)*(1+D/c^2)
  have hD : 0≤D := cubicThetaGaussianPowerConstant_nonneg
  have hA : 0≤A := by dsimp [A]; positivity
  change cubicThetaLatticeGaussianTail t≤(D+A)/t
  by_cases ht1 : t≤1
  · have hg := cubicThetaScalarGaussianReal_le 0 (div_pos ht (by norm_num : (0:ℝ)<9))
    rw [cubicThetaScalarGaussianReal_zero_tail ht] at hg
    have he : 4*Real.pi^2/(27*(t/9))=c/t := by dsimp [c]; ring
    have hk : 2*Real.pi/(9*Real.sqrt 3*(t/9))=(2*Real.pi/Real.sqrt 3)/t := by ring
    rw [he,hk] at hg
    have hT := cubicThetaLatticeGaussianTail_div_bound (c:=c) (by dsimp [c]; positivity) ht
    have ht2 : t^2≤1 := by nlinarith
    have hb : cubicThetaLatticeGaussianTail (c/t)≤D/c^2 :=
      hT.trans (by nlinarith [mul_nonneg (div_nonneg hD (sq_nonneg c)) (sub_nonneg.mpr ht2)])
    calc
      _ ≤ A/t := by
        have h := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hb)
          (show 0≤(2*Real.pi/Real.sqrt 3)/t by positivity)
        have hx : ((2*Real.pi/Real.sqrt 3)/t)*(1+D/c^2)=A/t := by dsimp [A]; ring
        rw [hx] at h
        linarith
      _ ≤ (D+A)/t := (div_le_div_iff_of_pos_right ht).mpr (by linarith)
  · have hlarge := cubicThetaLatticeGaussianTail_power_bound ht
    have ht1' : 1≤t := (lt_of_not_ge ht1).le
    apply hlarge.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos ht) ht).mpr
    nlinarith [mul_nonneg hD (sub_nonneg.mpr ht1'),mul_nonneg hA (sq_nonneg t)]

end CubicFirstMoment

end

end OAI
