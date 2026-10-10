import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarGaussianReal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarFactorization
import OAI.NumberTheory.CubicMoment.Estimates.ThetaHeatKernelBound

namespace OAI

/-! The actual affine four-dimensional Gaussian, before removal of common
primary factors. Its Mellin integral is the full height series. -/
noncomputable section
namespace CubicFirstMoment

def CubicThetaFullRow.quadratic (r : CubicThetaFullRow) (p : ℂ × ℝ) : ℝ :=
  (Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)/p.2

lemma CubicThetaFullRow.denominator_pos (r : CubicThetaFullRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    0<Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 := by
  by_cases hc : r.c=0
  · have hd := norm_pos_of_ne_zero (primary_ne_zero r.d_primary)
    simpa only [hc,Eisenstein.coe_zero,zero_mul,zero_add,norm,
      Complex.normSq_zero,mul_zero,add_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hp))

lemma CubicThetaFullRow.quadratic_pos (r : CubicThetaFullRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : 0<r.quadratic p := div_pos (r.denominator_pos hp) hp

lemma CubicThetaFullRow.height_eq_inv (r : CubicThetaFullRow) (p : ℂ × ℝ) :
    r.height p=(r.quadratic p)⁻¹ := by
  simp only [CubicThetaFullRow.height,CubicThetaFullRow.quadratic,inv_div]

def cubicThetaFullGaussian (p : ℂ × ℝ) (t : ℝ) : ℝ :=
  ∑' r : CubicThetaFullRow, Real.exp (-t*r.quadratic p)

lemma cubicThetaFullGaussian_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    Summable (fun r : CubicThetaFullRow => Real.exp (-t*r.quadratic p)) := by
  have hs := cubicThetaFullHeightMass_summable hp (s:=3) (by norm_num)
  have hb := hs.mul_left (6/t^3)
  apply hb.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro r
  have hq := r.quadratic_pos hp
  have h := power_exp_bound ht 3 (r.quadratic p) hq.le
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,mul_one] at h
  rw [r.height_eq_inv,Real.rpow_ofNat,inv_pow]
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hq 3)).mpr (by nlinarith [h])

lemma cubicThetaFullRowCoordinates_quadratic (a b : Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    (cubicThetaFullRowCoordinates a b).quadratic p=
      Complex.normSq (3*(a:ℂ)*p.1+1+3*(b:ℂ))/p.2+9*norm a*p.2 := by
  unfold CubicThetaFullRow.quadratic cubicThetaFullRowCoordinates
  simp only [Subalgebra.coe_mul,Subalgebra.coe_add,Eisenstein.coe_one]
  change (Complex.normSq ((3:ℂ)*(a:ℂ)*p.1+(1+3*(b:ℂ)))+
    norm ((3:Eisenstein)*a)*p.2^2)/p.2=_
  rw [norm_mul_eq,show norm (3:Eisenstein)=9 by change Complex.normSq (3:ℂ)=9; norm_num]
  rw [show 3*(a:ℂ)*p.1+(1+3*(b:ℂ))=3*(a:ℂ)*p.1+1+3*(b:ℂ) by ring]
  field_simp

lemma cubicThetaFullGaussian_reindex {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    cubicThetaFullGaussian p t=∑' a : Eisenstein,
      Real.exp (-9*t*p.2*norm a)*cubicThetaScalarGaussianReal (3*(a:ℂ)*p.1+1) (t/p.2) := by
  have hs := (cubicThetaFullRowEquiv.summable_iff).mpr (cubicThetaFullGaussian_summable hp ht)
  unfold cubicThetaFullGaussian
  rw [←cubicThetaFullRowEquiv.tsum_eq]
  change Summable (fun c : Eisenstein × Eisenstein =>
    Real.exp (-t*(cubicThetaFullRowEquiv c).quadratic p)) at hs
  rw [hs.tsum_prod]
  apply tsum_congr
  intro a
  rw [cubicThetaScalarGaussianReal,←tsum_mul_left]
  apply tsum_congr
  intro b
  change Real.exp (-t*(cubicThetaFullRowCoordinates a b).quadratic p)=_
  rw [cubicThetaFullRowCoordinates_quadratic a b hp,←Real.exp_add]
  congr 1
  ring

end CubicFirstMoment

end

end OAI
