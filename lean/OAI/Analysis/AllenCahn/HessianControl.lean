import OAI.Analysis.AllenCahn.Barriers

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma diffuseDefect_barrier_lower {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) {κ : ℝ} (hκ : 2 * Real.sqrt 2 < κ)
    (y x : Space n) :
    (diffuseDefect v y * Real.exp (-relativeDefectConstant n * sharpDefectRadius n κ)) *
      radialBarrier κ x ≤ diffuseDefect v (y + x) := by
  let R := sharpDefectRadius n κ
  let C := relativeDefectConstant n
  let A := diffuseDefect v y * Real.exp (-C * R)
  let f := fun z : Space n => A * radialBarrier κ z
  let g := fun z : Space n => diffuseDefect v (y + z)
  have hAp : 0 < A := mul_pos (hp y) (Real.exp_pos _)
  have hk : 0 < κ := lt_trans (by positivity) hκ
  have hC : 0 < C := relativeDefectConstant_pos n
  have hs := diffuseDefect_smooth hv hi
  have hbs := smooth_C2 (radialBarrier_smooth n κ)
  have hfs : ContDiff ℝ 2 f := contDiff_const.mul hbs
  have hgs : ContDiff ℝ 2 g := (smooth_C2 hs).comp (contDiff_const.add contDiff_id)
  have hgder (z : Space n) : fderiv ℝ g z = fderiv ℝ (diffuseDefect v) (y + z) := by
    have H := (hs.differentiable (by simp) (y+z)).hasFDerivAt.comp z
      ((hasFDerivAt_const y z).add (hasFDerivAt_id z))
    simpa only [g, Function.comp_def, zero_add, ContinuousLinearMap.comp_id] using H.fderiv
  have hglap (z : Space n) : Laplacian.laplacian g z = Laplacian.laplacian (diffuseDefect v) (y + z) :=
    laplacian_translate (smooth_C2 hs) y z
  have hg0 (z : Space n) : 0 ≤ g z := (hp (y+z)).le
  have hdecay : Tendsto f (Bornology.cobounded (Space n)) (𝓝 0) := by
    have H := (radialBarrier_decay (n := n) hk).const_mul A
    simpa only [mul_zero] using H
  have hinner (z : Space n) (hz : ‖z‖ ≤ R) : f z ≤ g z := by
    have H := diffuseDefect_exp_comparison_crude hv hi hAC hp (y+z) y
    have he : y - (y + z) = -z := by abel
    rw [he, norm_neg] at H
    have hex : Real.exp (C * ‖z‖) ≤ Real.exp (C * R) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hC.le)
    have HH : diffuseDefect v y ≤ Real.exp (C * R) * g z :=
      H.trans (mul_le_mul_of_nonneg_right hex (hg0 z))
    have HA : A ≤ g z := by
      have He := mul_le_mul_of_nonneg_left HH (Real.exp_pos (-C*R)).le
      have Hexp : Real.exp (-C*R) * Real.exp (C*R) = 1 := by
        rw [← Real.exp_add]
        have hh : -C * R + C * R = 0 := by ring
        rw [hh, Real.exp_zero]
      dsimp [A]
      nlinarith [He, Hexp]
    have hb1 : radialBarrier κ z ≤ 1 := by
      change Real.exp (-κ * smoothRadius z) ≤ 1
      exact Real.exp_le_one_iff.mpr (by nlinarith [smoothRadius_pos z])
    exact (mul_le_of_le_one_right hAp.le hb1).trans HA
  have hsub (z : Space n) (hz : R < ‖z‖) :
      -Laplacian.laplacian f z + fderiv ℝ f z (diffuseDrift v (y+z)) +
        defectPotential v (y+z) * f z < 0 := by
    have H := mul_neg_of_pos_of_neg hAp (radialBarrier_defect_subsolution (smooth_C2 hv) hi hAC hκ y z hz)
    dsimp only [f]
    rw [laplacian_fun_const_mul hbs, fderiv_const_mul (hbs.differentiable (by norm_num) z),
      smul_apply, smul_eq_mul]
    nlinarith
  have hsuper (z : Space n) : 0 ≤ -Laplacian.laplacian g z +
      fderiv ℝ g z (diffuseDrift v (y+z)) + defectPotential v (y+z) * g z := by
    rw [hglap, hgder]
    have H := diffuseDefect_drift_eq_source hv hi hAC (y+z)
    have H0 : 0 ≤ hessianSquare v (y+z) := by dsimp [hessianSquare]; positivity
    dsimp only [defectSource] at H
    change 0 ≤ -Laplacian.laplacian (diffuseDefect v) (y+z) +
      fderiv ℝ (diffuseDefect v) (y+z) (diffuseDrift v (y+z)) +
      defectPotential v (y+z) * diffuseDefect v (y+z)
    linarith
  exact exterior_comparison hfs hgs (fun z => diffuseDrift v (y+z))
    (fun z => defectPotential v (y+z)) R (fun z => defectPotential_nonneg hi (y+z))
    hg0 hdecay hinner hsub hsuper x

def sharpDefectConstant (n : ℕ) (γ : ℝ) : ℝ :=
  Real.exp (relativeDefectConstant n * sharpDefectRadius n (2 * Real.sqrt 2 + γ) +
    (2 * Real.sqrt 2 + γ))

theorem diffuseDefect_exponential_comparison {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) {γ : ℝ} (hγ : 0 < γ) (y z : Space n) :
    diffuseDefect v y ≤ sharpDefectConstant n γ *
      Real.exp ((2 * Real.sqrt 2 + γ) * ‖y - z‖) * diffuseDefect v z := by
  let κ := 2 * Real.sqrt 2 + γ
  let C := relativeDefectConstant n
  let R := sharpDefectRadius n κ
  have hκ : 2 * Real.sqrt 2 < κ := by dsimp [κ]; linarith
  have hk : 0 < κ := lt_trans (by positivity) hκ
  have H := diffuseDefect_barrier_lower hv hi hAC hp hκ y (z-y)
  have he : y + (z-y) = z := by abel
  rw [he] at H
  have Hexp : Real.exp (C * R + κ * smoothRadius (z-y)) *
      (Real.exp (-C * R) * radialBarrier κ (z-y)) = 1 := by
    dsimp [radialBarrier]
    rw [← Real.exp_add, ← Real.exp_add]
    have hh : C * R + κ * smoothRadius (z-y) + (-C*R + -κ*smoothRadius (z-y)) = 0 := by ring
    rw [hh, Real.exp_zero]
  have Hmul := mul_le_mul_of_nonneg_left H (Real.exp_pos (C * R + κ * smoothRadius (z-y))).le
  have H1 : diffuseDefect v y ≤ Real.exp (C * R + κ * smoothRadius (z-y)) * diffuseDefect v z := by
    calc diffuseDefect v y = diffuseDefect v y * 1 := (mul_one _).symm
      _ = diffuseDefect v y * (Real.exp (C * R + κ * smoothRadius (z-y)) *
          (Real.exp (-C * R) * radialBarrier κ (z-y))) := by rw [Hexp]
      _ = Real.exp (C * R + κ * smoothRadius (z-y)) *
          (diffuseDefect v y * Real.exp (-C * R) * radialBarrier κ (z-y)) := by ring
      _ ≤ _ := Hmul
  have H2 : Real.exp (C * R + κ * smoothRadius (z-y)) ≤
      Real.exp (C * R + κ) * Real.exp (κ * ‖y-z‖) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have HH := mul_le_mul_of_nonneg_left (smoothRadius_le_norm_add_one (z-y)) hk.le
    rw [norm_sub_rev z y] at HH
    linarith
  exact H1.trans (mul_le_mul_of_nonneg_right H2 (hp z).le)

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open scoped ContDiff

lemma positive_defect_log_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) :
    let h := fun y => Real.log (diffuseDefect v y)
    let r := fun y => defectSource v y / diffuseDefect v y
    (∀ x, Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2) ∧
    (∀ x, ‖gradient h x‖ ≤ relativeDefectConstant n) ∧
    (∀ i x, |coordDeriv r i x| ≤ 2 * defectSourceConstant n * (1 + relativeDefectConstant n)) := by
  dsimp only
  let D := diffuseDefect v
  let h := fun y => Real.log (D y)
  let r := fun y => defectSource v y / D y
  have hs := diffuseDefect_smooth hv hi
  have hd := hs.differentiable (by simp)
  have hne (x) : D x ≠ 0 := ne_of_gt (hp x)
  have hgb (x) : ‖gradient h x‖ ≤ relativeDefectConstant n := by
    dsimp only [h]
    rw [gradient_log (hd x) (hne x), norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hp x),
      inv_mul_eq_div]
    exact (div_le_iff₀ (hp x)).mpr (diffuseDefect_relative_gradient_bound hv hi hAC x)
  have hhi (i : Fin n) (x) : coordDeriv h i x = coordDeriv D i x / D x :=
    coordDeriv_log hd hne i x
  have hS := defectSourceConstant_pos n
  have hC := relativeDefectConstant_pos n
  have hc := defectSource_bounds hv hi hAC
  have hrb (x) : |r x| ≤ defectSourceConstant n := by
    dsimp [r]
    rw [abs_div, abs_of_pos (hp x)]
    exact (div_le_iff₀ (hp x)).mpr (hc.1 x)
  constructor
  · intro x
    rw [drift_log (smooth_C2 hs) hne, diffuseDefect_drift_eq_source hv hi hAC]
  constructor
  · exact hgb
  · intro i x
    change |coordDeriv r i x| ≤ _
    have hri : coordDeriv r i x = coordDeriv (defectSource v) i x / D x - r x * coordDeriv h i x := by
      dsimp only [r]
      rw [coordDeriv_div ((defectSource_smooth hv hi).differentiable (by simp)) hd hne, hhi]
      dsimp only [D]
      field_simp [ne_of_gt (hp x)]
    have hic : |coordDeriv h i x| ≤ relativeDefectConstant n :=
      (coordDeriv_abs_le_gradient h i x).trans (hgb x)
    have hsr : |coordDeriv (defectSource v) i x| / D x ≤
        defectSourceConstant n * (1 + relativeDefectConstant n) := by
      apply (div_le_iff₀ (hp x)).mpr
      have hg := (coordDeriv_abs_le_gradient D i x).trans
        (diffuseDefect_relative_gradient_bound hv hi hAC x)
      have hh := hc.2 i x
      dsimp only [D] at hg ⊢
      nlinarith
    rw [hri]
    apply (abs_sub _ _).trans
    rw [abs_div, abs_of_pos (hp x), abs_mul]
    have hm := mul_le_mul (hrb x) hic (abs_nonneg _) hS.le
    nlinarith

lemma drift_log_coordinate {n : ℕ} {v h r : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hh : ContDiff ℝ ∞ h) (hr : ContDiff ℝ ∞ r)
    (heq : ∀ x, Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2)
    (i : Fin n) (x : Space n) :
    Laplacian.laplacian (coordDeriv h i) x -
      fderiv ℝ (coordDeriv h i) x (diffuseDrift v x - (2 : ℝ) • gradient h x) =
      coordDeriv r i x + ∑ k : Fin n, coordDeriv (driftCoeff v k) i x * coordDeriv h k x := by
  have hw := gradient_norm_sq_smooth hh
  have H := diffuse_drift_commute hv hi hh (hr.sub hw) heq i x
  rw [coordDeriv_sub (hr.differentiable (by simp)) (hw.differentiable (by simp))] at H
  have hd : coordDeriv (fun y => ‖gradient h y‖ ^ 2) i x =
      2 * fderiv ℝ (coordDeriv h i) x (gradient h x) := by
    have he : (fun y => ‖gradient h y‖ ^ 2) = fun y => ∑ j : Fin n, coordDeriv h j y ^ 2 :=
      funext (gradient_norm_sq h)
    have hds (j : Fin n) := (coordDeriv_smooth hh j).differentiable (by simp)
    rw [he, coordDeriv_sum (f := fun j y => coordDeriv h j y ^ 2) _ (fun j _ => (hds j).pow 2)]
    rw [← inner_gradient_left, inner_gradient_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs : coordDeriv (fun y => coordDeriv h j y ^ 2) i x =
        2 * coordDeriv h j x * coordDeriv (coordDeriv h j) i x := by
      change fderiv ℝ (fun y => coordDeriv h j y ^ 2) x (basis n i) = _
      rw [fderiv_fun_pow 2 (hds j x)]
      simp [coordDeriv, mul_assoc]
    rw [hs, coordDeriv_comm (smooth_C2 hh) j i]
    ring
  rw [hd] at H
  rw [map_sub, map_smul, smul_eq_mul]
  linarith

def logDefectHessianConstant (n : ℕ) : ℝ :=
  2 * (2 * relativeDefectConstant n +
    (2 * defectSourceConstant n * (1 + relativeDefectConstant n) +
      n * (tensorCoeffConstant n * relativeDefectConstant n)) + 3) *
        (2 * Real.sqrt 2 + 2 * relativeDefectConstant n + 1)

lemma logDefectHessianConstant_pos (n : ℕ) : 0 < logDefectHessianConstant n := by
  have hC := relativeDefectConstant_pos n
  have hS := defectSourceConstant_pos n
  have hT := tensorCoeffConstant_pos n
  dsimp [logDefectHessianConstant]; positivity

lemma logDefect_hessian_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (i : Fin n) (x : Space n) :
    ‖gradient (coordDeriv (fun y => Real.log (diffuseDefect v y)) i) x‖ ≤ logDefectHessianConstant n := by
  let h := fun y => Real.log (diffuseDefect v y)
  let r := fun y => defectSource v y / diffuseDefect v y
  let C := relativeDefectConstant n
  let S := 2 * defectSourceConstant n * (1 + C) + n * (tensorCoeffConstant n * C)
  let B := 2 * Real.sqrt 2 + 2 * C
  have hC : 0 ≤ C := (relativeDefectConstant_pos n).le
  have hS : 0 ≤ S := by have := (defectSourceConstant_pos n).le; have := (tensorCoeffConstant_pos n).le; dsimp [S]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hne (y) : diffuseDefect v y ≠ 0 := ne_of_gt (hp y)
  have hh : ContDiff ℝ ∞ h := (diffuseDefect_smooth hv hi).log hne
  have hr : ContDiff ℝ ∞ r := (defectSource_smooth hv hi).div (diffuseDefect_smooth hv hi) hne
  obtain ⟨heq,hgb,hrb⟩ := positive_defect_log_bounds hv hi hAC hp
  have hcb (k : Fin n) (y) : |coordDeriv h k y| ≤ C :=
    (coordDeriv_abs_le_gradient h k y).trans (hgb y)
  have hdb (y) : ‖diffuseDrift v y - (2 : ℝ) • gradient h y‖ ≤ B := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact add_le_add (diffuseDrift_bound (smooth_C2 hv) hi hAC y) (mul_le_mul_of_nonneg_left (hgb y) (by norm_num))
  have hpb (y) : |Laplacian.laplacian (coordDeriv h i) y -
      fderiv ℝ (coordDeriv h i) y (diffuseDrift v y - (2 : ℝ) • gradient h y)| ≤ S := by
    rw [drift_log_coordinate hv hi hh hr heq i y]
    apply (abs_add_le _ _).trans (add_le_add (hrb i y) _)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc (∑ k : Fin n, |coordDeriv (driftCoeff v k) i y * coordDeriv h k y|) ≤
        ∑ k : Fin n, tensorCoeffConstant n * C := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul ((tensorCoeff_C1Bound hv hi hAC).2.2.2.2 k |>.2 i y)
            (hcb k y) (abs_nonneg _) (tensorCoeffConstant_pos n).le
      _ = n * (tensorCoeffConstant n * C) := by simp
  exact PoissonSupport.DeGiorgi.bounded_drift_gradient (smooth_C2 (coordDeriv_smooth hh i))
    (fun y => diffuseDrift v y - (2 : ℝ) • gradient h y) hC hS hB (hcb i) hdb hpb x

def relativeHessianConstant (n : ℕ) : ℝ :=
  n * (relativeDefectConstant n ^ 2 + logDefectHessianConstant n)

theorem diffuseDefect_relative_hessian_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (i : Fin n) (x : Space n) :
    ‖gradient (coordDeriv (diffuseDefect v) i) x‖ ≤ relativeHessianConstant n * diffuseDefect v x := by
  let D := diffuseDefect v
  let h := fun y => Real.log (D y)
  have hne (y) : D y ≠ 0 := ne_of_gt (hp y)
  have hs := diffuseDefect_smooth hv hi
  have hd := hs.differentiable (by simp)
  have hh : ContDiff ℝ ∞ h := hs.log hne
  have hhd (i : Fin n) := (coordDeriv_smooth hh i).differentiable (by simp)
  have hgb := (positive_defect_log_bounds hv hi hAC hp).2.1
  have hic (j : Fin n) : |coordDeriv h j x| ≤ relativeDefectConstant n :=
    (coordDeriv_abs_le_gradient h j x).trans (hgb x)
  have he (j : Fin n) : coordDeriv D j = fun y => D y * coordDeriv h j y := by
    funext y
    rw [show coordDeriv h j y = coordDeriv D j y / D y from coordDeriv_log hd hne j y]
    field_simp [hne y]
  have hc (j : Fin n) : |coordDeriv (coordDeriv D i) j x| ≤
      (relativeDefectConstant n ^ 2 + logDefectHessianConstant n) * D x := by
    rw [he i, coordDeriv_mul hd (hhd i)]
    have hDi := (coordDeriv_abs_le_gradient D j x).trans
      (diffuseDefect_relative_gradient_bound hv hi hAC x)
    have hH := (coordDeriv_abs_le_gradient (coordDeriv h i) j x).trans
      (logDefect_hessian_bound hv hi hAC hp i x)
    have hm₁ := mul_le_mul hDi (hic i) (abs_nonneg _) (mul_nonneg (relativeDefectConstant_pos n).le (hp x).le)
    have hm₂ := mul_le_mul_of_nonneg_left hH (hp x).le
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_pos (hp x)]
    nlinarith
  apply (gradient_norm_le_sum_abs _ x).trans
  calc (∑ j : Fin n, |coordDeriv (coordDeriv D i) j x|) ≤
      ∑ j : Fin n, (relativeDefectConstant n ^ 2 + logDefectHessianConstant n) * D x :=
      Finset.sum_le_sum fun j _ => hc j
    _ = relativeHessianConstant n * D x := by simp [relativeHessianConstant]; ring

lemma carrier_gradient_estimate {n : ℕ} {f d : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hd : ContDiff ℝ 2 d) (hp : ∀ x, 0 < d x)
    (b : Space n → Space n) {M C B G V : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G) (hV : 0 ≤ V)
    (hfb : ∀ x, |f x| ≤ M * d x) (hbb : ∀ x, ‖b x‖ ≤ B)
    (hgb : ∀ x, ‖gradient d x‖ ≤ G * d x)
    (hfL : ∀ x, |Laplacian.laplacian f x - fderiv ℝ f x (b x)| ≤ C * d x)
    (hdL : ∀ x, |Laplacian.laplacian d x - fderiv ℝ d x (b x)| ≤ V * d x)
    (x : Space n) :
    ‖gradient f x‖ ≤
      (2 * (2 * M + (C + M * V) + 3) * (B + 2 * G + 1) + M * G) * d x := by
  let w := fun y => f y / d y
  let b' := fun y => b y - (2 / d y) • gradient d y
  have hne y : d y ≠ 0 := ne_of_gt (hp y)
  have hw : ContDiff ℝ 2 w := hf.div hd hne
  have hwb (y) : |w y| ≤ M := by
    dsimp [w]; rw [abs_div, abs_of_pos (hp y)]
    exact (div_le_iff₀ (hp y)).mpr (hfb y)
  have hb' (y) : ‖b' y‖ ≤ B + 2 * G := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) (hp y))]
    apply add_le_add (hbb y)
    calc (2 / d y) * ‖gradient d y‖ ≤ (2 / d y) * (G * d y) :=
        mul_le_mul_of_nonneg_left (hgb y) (div_nonneg (by norm_num) (hp y).le)
      _ = 2 * G := by field_simp [hne y]
  have hwL (y) : |Laplacian.laplacian w y - fderiv ℝ w y (b' y)| ≤ C + M * V := by
    have H := drift_quotient_identity hf hd hne b y
    change d y * (Laplacian.laplacian w y - fderiv ℝ w y (b' y)) = _ at H
    have Habs := congrArg abs H
    rw [abs_mul, abs_of_pos (hp y)] at Habs
    have hm := mul_le_mul (hwb y) (hdL y) (abs_nonneg _) hM
    have hm' : |w y * (Laplacian.laplacian d y - fderiv ℝ d y (b y))| ≤ M * (V * d y) := by
      rw [abs_mul]; exact hm
    have hh := (abs_sub (Laplacian.laplacian f y - fderiv ℝ f y (b y))
      (w y * (Laplacian.laplacian d y - fderiv ℝ d y (b y)))).trans (add_le_add (hfL y) hm')
    rw [← Habs] at hh
    nlinarith [hp y]
  have hgw := PoissonSupport.DeGiorgi.bounded_drift_gradient hw b' hM
    (add_nonneg hC (mul_nonneg hM hV)) (add_nonneg hB (mul_nonneg (by norm_num) hG))
    hwb hb' hwL x
  have he : f = fun y => w y * d y := by
    funext y; dsimp [w]; field_simp [hne y]
  have hg : gradient f x = w x • gradient d x + d x • gradient w x := by
    rw [he]
    simp only [gradient, fderiv_fun_mul (hw.differentiable (by norm_num) x) (hd.differentiable (by norm_num) x), map_add, map_smul]
  rw [hg]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hp x)]
  have hm₁ := mul_le_mul (hwb x) (hgb x) (norm_nonneg _) hM
  have hm₂ := mul_le_mul_of_nonneg_left hgw (hp x).le
  nlinarith

end DeGiorgi
end

end OAI
