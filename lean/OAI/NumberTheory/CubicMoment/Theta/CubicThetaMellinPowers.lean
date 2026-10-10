import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothMellin

namespace OAI

/-! Exact positive-real power bookkeeping for the additive theta transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_cpow_affine {r : ℝ} (hr : 0<r) (j : ℝ) (c s : ℂ) :
    (r:ℂ)^((j:ℂ)*s+c) = (r:ℂ)^c*((r^j:ℝ):ℂ)^s := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_mul_ofReal_nonneg hr.le]
  ring

def cubicThetaDualScale (q : Eisenstein) (Z : ℝ) : ℝ :=
  (2*Real.pi)^4*(cubicThetaLevelScale q)^4*Z

def cubicThetaDualPrefactor (q : Eisenstein) : ℂ :=
  (cubicThetaLevelScale q:ℂ)^(-2:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2:ℂ)

lemma cubicThetaDualPrefactor_ne_zero {q : Eisenstein} (hq : primary q) :
    cubicThetaDualPrefactor q≠0 := by
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))

lemma cubicThetaDualScale_pos {q : Eisenstein} (hq : primary q) {Z : ℝ} (hZ : 0<Z) :
    0<cubicThetaDualScale q Z := by
  unfold cubicThetaDualScale
  positivity [cubicThetaLevelScale_pos hq]

lemma cubicTheta_dual_power {q : Eisenstein} (hq : primary q) {Z r : ℝ}
    (hZ : 0<Z) (hr : 0<r) (s : ℂ) :
    (Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
      ((2*Real.pi:ℝ):ℂ)^(4*s-2)*(r:ℂ)^(-(2*(1-s)-1)) =
    (cubicThetaLevelScale q:ℂ)^(-2:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2:ℂ)*(r:ℂ)^(-1:ℂ)*
      ((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^s := by
  have hρ := cubicThetaLevelScale_pos hq
  have hπ : 0<2*Real.pi := by positivity
  have hp (v : ℝ) (hv : 0<v) :
      (v:ℂ)^(4*s-2) = (v:ℂ)^(-2:ℂ)*((v^4:ℝ):ℂ)^s := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_neg,sub_eq_add_neg,
      Real.rpow_ofNat] using cubicTheta_cpow_affine hv 4 (-2) s
  have hrp : (r:ℂ)^(-(2*(1-s)-1)) = (r:ℂ)^(-1:ℂ)*((r^2:ℝ):ℂ)^s := by
    have H := cubicTheta_cpow_affine hr 2 (-1) s
    norm_num only [Complex.ofReal_ofNat,Real.rpow_ofNat] at H
    rw [show -(2*(1-s)-1)=(2:ℂ)*s+ -1 by ring]
    exact H
  rw [hp _ hρ,hp _ hπ,hrp]
  have hm (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      ((u*v:ℝ):ℂ)^s=(u:ℂ)^s*(v:ℂ)^s := by
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hu hv]
  simp only [cubicThetaDualScale]
  rw [hm _ _ (by positivity) (sq_nonneg r),
    hm _ _ (by positivity) hZ.le,hm _ _ (by positivity) (by positivity)]
  ring

lemma cubicTheta_archimedean_power {q : Eisenstein} (hq : primary q) {Z : ℝ}
    (hZ : 0<Z) (s : ℂ) :
    (Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
      ((2*Real.pi:ℝ):ℂ)^(4*s-2) =
        cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s := by
  simpa only [Complex.ofReal_one,Complex.one_cpow,mul_one,one_pow,
    cubicThetaDualPrefactor] using cubicTheta_dual_power hq hZ (r:=1) zero_lt_one s

end CubicFirstMoment

end

end OAI
