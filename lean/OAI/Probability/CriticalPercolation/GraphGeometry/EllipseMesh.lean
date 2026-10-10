import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.EuclideanEllipse

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

lemma normalize_basis (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W c z=z.re•normalize R W c 1+z.im•normalize R W c Complex.I := by
  have hz : z=z.re•(1 : ℂ)+z.im•Complex.I := by
    apply Complex.ext <;> simp
  rw [hz,normalize_real_linear]
  simp

lemma basis_difference_bound (R W R' W' : ℝ) (c d : Circle) (q : ℝ) (hq : 0≤q)
    (h1 : ‖normalize R W c 1-normalize R' W' d 1‖≤q)
    (hI : ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖≤q) (z : ℂ) :
    ‖normalize R W c z-normalize R' W' d z‖≤2*q*‖z‖ := by
  have he : normalize R W c z-normalize R' W' d z=
      z.re•(normalize R W c 1-normalize R' W' d 1)+
      z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I) := by
    rw [normalize_basis R W c z,normalize_basis R' W' d z]
    simp only [smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖z.re•(normalize R W c 1-normalize R' W' d 1)‖+
      ‖z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I)‖ := norm_add_le _ _
    _ = |z.re| * ‖normalize R W c 1-normalize R' W' d 1‖+
      |z.im| * ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ |z.re| * q+|z.im| * q := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ ≤ 2*q*‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) hq,
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) hq]

def diskRadius (W U : ℝ) (p : ℝ×ℝ) : ℝ := W+(U-W)*p.1

def diskNormalize (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  normalize (diskRadius W U p) W (Circle.exp p.2)

def diskExpand (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  expand (diskRadius W U p) W (Circle.exp p.2)

def parameterDisk : Set (ℝ×ℝ) := Set.Icc (0,0) (1,Real.pi)

lemma diskRadius_bounds (W U : ℝ) (hWU : W≤U) {p : ℝ×ℝ} (hp : p∈parameterDisk) :
    W≤diskRadius W U p ∧ diskRadius W U p≤U := by
  obtain ⟨⟨hs,_hφ⟩,hs',_hφ'⟩ := hp
  dsimp [diskRadius]
  constructor <;> nlinarith

lemma diskNormalize_continuousOn (W U : ℝ) (hW : 0<W) (hWU : W≤U) (z : ℂ) :
    ContinuousOn (fun p => diskNormalize W U p z) parameterDisk := by
  have hR : ∀ p∈parameterDisk, diskRadius W U p≠0 := fun p hp =>
    ne_of_gt (hW.trans_le (diskRadius_bounds W U hWU hp).1)
  have hc : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)) := by
    simp only [Circle.coe_exp]
    fun_prop
  have hcinv : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)⁻¹) :=
    hc.inv₀ (fun p => (Circle.exp p.2).coe_ne_zero)
  have hRd : ContinuousOn (fun p => 1/diskRadius W U p) parameterDisk := by
    apply continuousOn_const.div
    · unfold diskRadius
      fun_prop
    · exact hR
  unfold diskNormalize normalize diagonal
  apply hc.continuousOn.mul
  have hre := hRd.mul (Complex.continuous_re.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have him := (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => 1/W) parameterDisk).mul
    (Complex.continuous_im.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have hd := (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => Complex.I) parameterDisk))
  convert hd using 1
  funext p
  apply Complex.ext <;> simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add,sub_zero]

theorem diskNormalize_uniform_comparison (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ delta : ℝ, 0<delta ∧ ∀ p∈parameterDisk, ∀ q∈parameterDisk,
      dist p q<delta → ∀ z : ℂ,
        ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖ := by
  let F : (ℝ×ℝ) → (ℂ × ℂ) := fun p => (diskNormalize W U p 1,diskNormalize W U p Complex.I)
  have hc : ContinuousOn F parameterDisk := (diskNormalize_continuousOn W U hW hWU 1).prodMk
    (diskNormalize_continuousOn W U hW hWU Complex.I)
  have hcompact : IsCompact parameterDisk := isCompact_Icc
  have hu := hcompact.uniformContinuousOn_of_continuous hc
  have hU : 0<U := hW.trans_le hWU
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (zeta/(2*U)) (by positivity)
  refine ⟨delta,hdelta,?_⟩
  intro p hp q hq hpq z
  have h := hclose p hp q hq hpq
  rw [Prod.dist_eq] at h
  have h1 : ‖diskNormalize W U p 1-diskNormalize W U q 1‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_left _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hI : ‖diskNormalize W U p Complex.I-diskNormalize W U q Complex.I‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_right _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hnorm := basis_difference_bound (diskRadius W U p) W (diskRadius W U q) W
    (Circle.exp p.2) (Circle.exp q.2) (zeta/(2*U)) (by positivity) h1 hI (diskExpand W U q z)
  have hqR := diskRadius_bounds W U hWU hq
  have hexpand : ‖diskExpand W U q z‖≤U*‖z‖ :=
    (expand_norm_le (diskRadius W U q) W hW.le hqR.1 (Circle.exp q.2) z).trans
      (mul_le_mul_of_nonneg_right hqR.2 (norm_nonneg _))
  have hcancel : diskNormalize W U q (diskExpand W U q z)=z :=
    normalize_expand _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ z
  change ‖diskNormalize W U p (diskExpand W U q z)-diskNormalize W U q (diskExpand W U q z)‖≤_ at hnorm
  rw [hcancel] at hnorm
  apply hnorm.trans
  have hmul := mul_le_mul_of_nonneg_left hexpand (by positivity : 0≤2*(zeta/(2*U)))
  convert hmul using 1
  field_simp

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
