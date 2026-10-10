import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHermitianMetric

namespace OAI

/-! The two-point metric identity gives exact scaling of Euclidean squared
lengths under the actual hyperbolic action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaRadius_smul (t : ℝ) (u : ℂ × ℝ) :
    cubicThetaRadius (t • u)=t^2*cubicThetaRadius u := by
  change Complex.normSq ((t:ℂ)*u.1)+(t*u.2)^2=t^2*(Complex.normSq u.1+u.2^2)
  rw [Complex.normSq_mul,Complex.normSq_ofReal]
  ring

lemma cubicThetaRadius_continuous : Continuous cubicThetaRadius := by
  unfold cubicThetaRadius
  fun_prop

lemma cubicThetaMobius_secant_scale (g : SL(2,ℂ)) {p u : ℂ × ℝ}
    (hp : 0<p.2) {t : ℝ} (ht : t≠0) (hq : 0<(p+t • u).2) :
    cubicThetaRadius (t⁻¹ • (cubicThetaMobius g (p+t • u)-cubicThetaMobius g p))*
        ((p+t • u).2*p.2)=
      cubicThetaRadius u*((cubicThetaMobius g (p+t • u)).2*(cubicThetaMobius g p).2) := by
  have h := cubicThetaHyperbolicChord_invariant g hq hp
  change cubicThetaRadius (cubicThetaMobius g (p+t • u)-cubicThetaMobius g p)/
    ((cubicThetaMobius g (p+t • u)).2*(cubicThetaMobius g p).2)=
    cubicThetaRadius (p+t • u-p)/((p+t • u).2*p.2) at h
  have hd := mul_ne_zero (cubicThetaMobius_height_pos g hq).ne'
    (cubicThetaMobius_height_pos g hp).ne'
  have hd' := mul_ne_zero hq.ne' hp.ne'
  rw [div_eq_div_iff hd hd'] at h
  have he : p+t • u-p=t • u := by abel
  rw [he,cubicThetaRadius_smul] at h
  rw [cubicThetaRadius_smul]
  field_simp
  nlinarith [h]

end CubicFirstMoment

end

end OAI
