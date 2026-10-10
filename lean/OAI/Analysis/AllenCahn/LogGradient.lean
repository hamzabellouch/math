import OAI.Analysis.AllenCahn.RelativeDerivatives

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma bounded_log_gradient {n : ℕ} {v h r : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hh : ContDiff ℝ ∞ h) (hr : ContDiff ℝ ∞ r) {R C B M : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (heq : ∀ x, Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2)
    (hrb : ∀ x, |r x| ≤ R)
    (hrdb : ∀ i x, |coordDeriv r i x| ≤ R * (1 + |coordDeriv h i x|))
    (hcb : ∀ i k x, |coordDeriv (driftCoeff v k) i x| ≤ C)
    (hbb : ∀ x, ‖diffuseDrift v x‖ ≤ B)
    (hgb : ∀ x, ‖gradient h x‖ ≤ M) :
    ∀ x, ‖gradient h x‖ ^ 2 ≤
      (3 * (n + 1)) * (6 * R ^ 2 + 6 * B ^ 2 + R * n + 3 * R + 2 * C * n + 2) := by
  let A := 6 * R ^ 2 + 6 * B ^ 2 + R * n + 3 * R + 2 * C * n + 1
  let N : ℝ := 3 * (n + 1)
  let w := fun y => ‖gradient h y‖ ^ 2
  let b := fun y => diffuseDrift v y - (2 : ℝ) • gradient h y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hw := smooth_C2 (gradient_norm_sq_smooth hh)
  have hwb (x : Space n) : |w x| ≤ M ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgb x) 2
  have hbb' (x : Space n) : ‖b x‖ ≤ B + 2 * M := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact add_le_add (hbb x) (mul_le_mul_of_nonneg_left (hgb x) (by norm_num))
  have hpde (x : Space n) : w x ^ 2 - A * N * w x - A * N ^ 2 ≤
      N * (Laplacian.laplacian w x - fderiv ℝ w x (b x)) := by
    let H := ∑ i : Fin n, ‖gradient (coordDeriv h i) x‖ ^ 2
    let t := fderiv ℝ h x (diffuseDrift v x)
    have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hw0 : 0 ≤ w x := sq_nonneg _
    have htrace := laplacian_sq_le_hessian hh x
    have ht : |t| ≤ ‖gradient h x‖ * B := by
      dsimp [t]
      rw [← inner_gradient_left]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hbb x) (norm_nonneg _))
    have ht2 : t ^ 2 ≤ B ^ 2 * w x := by
      have hh' := pow_le_pow_left₀ (abs_nonneg t) ht 2
      simp only [sq_abs] at hh'
      dsimp [w]; nlinarith
    have hr2 : r x ^ 2 ≤ R ^ 2 := by
      have hh' := pow_le_pow_left₀ (abs_nonneg (r x)) (hrb x) 2
      simpa only [sq_abs] using hh'
    have he := heq x
    change Laplacian.laplacian h x - t = r x - w x at he
    have htr : w x ^ 2 ≤ 3 * R ^ 2 + 3 * B ^ 2 * w x + N * H := by
      have hs1 := sq_nonneg (r x - t)
      have hs2 := sq_nonneg (r x + Laplacian.laplacian h x)
      have hs3 := sq_nonneg (t + Laplacian.laplacian h x)
      change Laplacian.laplacian h x ^ 2 ≤ n * H at htrace
      dsimp [N]
      nlinarith
    have hlo := log_bochner_lower hv hi hh hr hR hC heq hrdb hcb x
    change 2 * H - R * n - (3 * R + 2 * C * n) * w x ≤
      Laplacian.laplacian w x - fderiv ℝ w x (b x) at hlo
    have hlo' := mul_le_mul_of_nonneg_left hlo hN.le
    have hAc : 6 * R ^ 2 + R * n ≤ A := by
      dsimp [A]
      have hc : 0 ≤ C * n := by positivity
      nlinarith [sq_nonneg B]
    have hAl : 6 * B ^ 2 + 3 * R + 2 * C * n ≤ A := by
      dsimp [A]
      have hp : 0 ≤ R * n := by positivity
      nlinarith [sq_nonneg R]
    have hAc' := mul_le_mul_of_nonneg_left hAc hN.le
    have hAl' := mul_le_mul_of_nonneg_left hAl hN.le
    have hc1 := mul_nonneg (sub_nonneg.mpr hN1) (sq_nonneg R)
    have hc2 := mul_nonneg (sub_nonneg.mpr hN1) (sq_nonneg B)
    have hc3 := mul_nonneg (mul_nonneg hA hN.le) (sub_nonneg.mpr hN1)
    have hc4 : 0 ≤ (A * N - (6 * B ^ 2 + N * (3 * R + 2 * C * n))) * w x := by
      apply mul_nonneg _ hw0
      nlinarith
    nlinarith [sq_nonneg (w x)]
  have HH := bounded_drift_logistic_scaled hw b (sq_nonneg M) (by positivity) hA hN hwb hbb' hpde
  intro x
  convert HH x using 1; dsimp [A,N,w]; ring

lemma coordDeriv_div {n : ℕ} {f g : Space n → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hne : ∀ x, g x ≠ 0) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => f y / g y) i x =
      (g x * coordDeriv f i x - f x * coordDeriv g i x) / g x ^ 2 := by
  have hi := (hasDerivAt_inv (hne x)).comp_hasFDerivAt x (hg x).hasFDerivAt
  have hh := ((hf x).hasFDerivAt.mul hi).fderiv
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (basis n i)) hh
  change fderiv ℝ (fun y => f y * (g y)⁻¹) x (basis n i) = _
  rw [show (fun y => f y * (g y)⁻¹) = f * (Inv.inv ∘ g) from rfl, hh]
  simp only [add_apply, smul_apply, smul_smul, smul_eq_mul, Function.comp_def, coordDeriv]
  field_simp [hne x]; ring

lemma coordDeriv_log {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (hne : ∀ x, f x ≠ 0) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => Real.log (f y)) i x = coordDeriv f i x / f x := by
  simp only [coordDeriv, fderiv.log (hf x) (hne x), smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

lemma gradient_log {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hne : f x ≠ 0) :
    gradient (fun y => Real.log (f y)) x = (f x)⁻¹ • gradient f x := by
  simp only [gradient, fderiv.log hf hne, map_smul]

lemma laplacian_log {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (hne : ∀ x, f x ≠ 0) (x : Space n) :
    Laplacian.laplacian (fun y => Real.log (f y)) x =
      Laplacian.laplacian f x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2 := by
  have hd := hf.differentiable (by norm_num)
  have he (i : Fin n) : coordDeriv (fun y => Real.log (f y)) i =
      fun y => coordDeriv f i y / f y := funext (coordDeriv_log hd hne i)
  rw [laplacian_eq_sum_coordDeriv (hf.log hne)]
  simp_rw [he, coordDeriv_div ((coordDeriv_contDiff hf _).differentiable (by norm_num)) hd hne]
  rw [laplacian_eq_sum_coordDeriv hf, gradient_norm_sq, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hne x]

lemma drift_log {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (hne : ∀ x, f x ≠ 0) (b : Space n → Space n) (x : Space n) :
    Laplacian.laplacian (fun y => Real.log (f y)) x -
      fderiv ℝ (fun y => Real.log (f y)) x (b x) =
    (Laplacian.laplacian f x - fderiv ℝ f x (b x)) / f x -
      ‖gradient (fun y => Real.log (f y)) x‖ ^ 2 := by
  rw [laplacian_log hf hne, fderiv.log (hf.differentiable (by norm_num) x) (hne x),
    gradient_log (hf.differentiable (by norm_num) x) (hne x)]
  simp only [smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  ring

lemma gradient_add_const {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (x : Space n) : gradient (fun y => f y + c) x = gradient f x := by
  simp only [gradient, fderiv_fun_add (hf x) (differentiableAt_const c), fderiv_const_apply, add_zero]

lemma coordDeriv_add_const {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => f y + c) i x = coordDeriv f i x := by
  simp only [coordDeriv, fderiv_fun_add (hf x) (differentiableAt_const c), fderiv_const_apply, add_zero]

lemma regularized_defect_log_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    {δ : ℝ} (hδ : 0 < δ) :
    let e := fun y => diffuseDefect v y + δ
    let h := fun y => Real.log (e y)
    let r := fun y => defectSource v y / e y
    (∀ x, Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2) ∧
    (∀ x, |r x| ≤ 2 * defectSourceConstant n) ∧
    (∀ i x, |coordDeriv r i x| ≤ 2 * defectSourceConstant n * (1 + |coordDeriv h i x|)) := by
  dsimp only
  let e := fun y => diffuseDefect v y + δ
  let h := fun y => Real.log (e y)
  let r := fun y => defectSource v y / e y
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC
  have hep (x : Space n) : 0 < e x := by dsimp [e]; linarith [hD x]
  have hene (x : Space n) : e x ≠ 0 := ne_of_gt (hep x)
  have hes : ContDiff ℝ ∞ e := (diffuseDefect_smooth hv hi).add contDiff_const
  have hed := hes.differentiable (by simp)
  have hDd := (diffuseDefect_smooth hv hi).differentiable (by simp)
  have hsd := (defectSource_smooth hv hi).differentiable (by simp)
  have hc := defectSource_bounds hv hi hAC
  have hS := defectSourceConstant_pos n
  have hde (x : Space n) : diffuseDefect v x ≤ e x := by dsimp [e]; linarith
  have hrv (x : Space n) : |r x| ≤ defectSourceConstant n := by
    dsimp [r]
    rw [abs_div, abs_of_pos (hep x)]
    apply (div_le_iff₀ (hep x)).mpr
    exact (hc.1 x).trans (mul_le_mul_of_nonneg_left (hde x) hS.le)
  have hei (i : Fin n) (x : Space n) : coordDeriv e i x = coordDeriv (diffuseDefect v) i x :=
    coordDeriv_add_const hDd δ i x
  have hhi (i : Fin n) (x : Space n) : coordDeriv h i x = coordDeriv (diffuseDefect v) i x / e x := by
    rw [show h = fun y => Real.log (e y) from rfl, coordDeriv_log hed hene, hei]
  constructor
  · intro x
    change Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2
    rw [show h = fun y => Real.log (e y) from rfl, drift_log (smooth_C2 hes) hene]
    congr 2
    rw [show e = fun y => diffuseDefect v y + δ from rfl,
      laplacian_fun_add (smooth_C2 (diffuseDefect_smooth hv hi)) contDiff_const]
    simp only [InnerProductSpace.laplacian_const, add_zero,
      fderiv_fun_add (hDd x) (differentiableAt_const δ), fderiv_const_apply]
    simpa using diffuseDefect_drift_eq_source hv hi hAC x
  constructor
  · intro x
    exact (hrv x).trans (by linarith)
  · intro i x
    change |coordDeriv r i x| ≤ _
    have hri : coordDeriv r i x = coordDeriv (defectSource v) i x / e x - r x * coordDeriv h i x := by
      dsimp only [r]
      rw [coordDeriv_div hsd hed hene, hei, hhi]
      field_simp [hene x]
    have hsi : |coordDeriv (defectSource v) i x| / e x ≤
        defectSourceConstant n * (1 + |coordDeriv h i x|) := by
      rw [hhi, abs_div, abs_of_pos (hep x)]
      apply (div_le_iff₀ (hep x)).mpr
      have hm := mul_le_mul_of_nonneg_left (hde x) hS.le
      have heq : defectSourceConstant n * (1 + |coordDeriv (diffuseDefect v) i x| / e x) * e x =
          defectSourceConstant n * e x + defectSourceConstant n * |coordDeriv (diffuseDefect v) i x| := by
        field_simp [hene x]
      rw [heq]
      nlinarith [hc.2 i x]
    rw [hri]
    calc |coordDeriv (defectSource v) i x / e x - r x * coordDeriv h i x| ≤
        |coordDeriv (defectSource v) i x / e x| + |r x * coordDeriv h i x| := abs_sub _ _
      _ ≤ defectSourceConstant n * (1 + |coordDeriv h i x|) + defectSourceConstant n * |coordDeriv h i x| := by
        rw [abs_div, abs_of_pos (hep x), abs_mul]
        exact add_le_add hsi (mul_le_mul_of_nonneg_right (hrv x) (abs_nonneg _))
      _ ≤ _ := by nlinarith

def relativeDefectConstant (n : ℕ) : ℝ :=
  (3 * (n + 1)) * (6 * (2 * defectSourceConstant n) ^ 2 + 6 * (2 * Real.sqrt 2) ^ 2 +
    (2 * defectSourceConstant n) * n + 3 * (2 * defectSourceConstant n) +
    2 * tensorCoeffConstant n * n + 2) + 1

lemma relativeDefectConstant_pos (n : ℕ) : 0 < relativeDefectConstant n := by
  have hS := defectSourceConstant_pos n
  have hC := tensorCoeffConstant_pos n
  dsimp [relativeDefectConstant]; positivity

lemma regularized_defect_gradient_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    {δ : ℝ} (hδ : 0 < δ) (x : Space n) :
    ‖gradient (diffuseDefect v) x‖ ≤ relativeDefectConstant n * (diffuseDefect v x + δ) := by
  let e := fun y => diffuseDefect v y + δ
  let h := fun y => Real.log (e y)
  let r := fun y => defectSource v y / e y
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC
  have hep (y : Space n) : 0 < e y := by dsimp [e]; linarith [hD y]
  have hene (y : Space n) : e y ≠ 0 := ne_of_gt (hep y)
  have heδ (y : Space n) : δ ≤ e y := by dsimp [e]; linarith [hD y]
  have hDs := diffuseDefect_smooth hv hi
  have hDd := hDs.differentiable (by simp)
  have hes : ContDiff ℝ ∞ e := hDs.add contDiff_const
  have hhs : ContDiff ℝ ∞ h := hes.log hene
  have hrs : ContDiff ℝ ∞ r := (defectSource_smooth hv hi).div hes hene
  have hn (y : Space n) : ‖gradient h y‖ = ‖gradient (diffuseDefect v) y‖ / e y := by
    dsimp only [h]
    rw [gradient_log (hes.differentiable (by simp) y) (hene y),
      gradient_add_const hDd δ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hep y)]
    ring
  let G : ℝ := 2 * n ^ 2 * (12 * (2 * Real.sqrt 2 + 1))
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hgb (y : Space n) : ‖gradient h y‖ ≤ G / δ := by
    rw [hn]
    apply (div_le_div_of_nonneg_right (diffuseDefect_gradient_uniform_bound hv hi hAC y) (hep y).le).trans
    exact div_le_div_of_nonneg_left hG hδ (heδ y)
  obtain ⟨hpde,hrb,hrdb⟩ := regularized_defect_log_bounds hv hi hAC hδ
  have hS := defectSourceConstant_pos n
  have hC := tensorCoeffConstant_pos n
  have hcb (i k : Fin n) (y : Space n) : |coordDeriv (driftCoeff v k) i y| ≤ tensorCoeffConstant n :=
    (tensorCoeff_C1Bound hv hi hAC).2.2.2.2 k |>.2 i y
  have hbb (y : Space n) : ‖diffuseDrift v y‖ ≤ 2 * Real.sqrt 2 := diffuseDrift_bound (smooth_C2 hv) hi hAC y
  have HH := bounded_log_gradient hv hi hhs hrs (show 0 ≤ 2 * defectSourceConstant n by positivity)
    hC.le (show 0 ≤ 2 * Real.sqrt 2 by positivity) (div_nonneg hG hδ.le) hpde hrb hrdb hcb hbb hgb x
  have hQ : 0 ≤ relativeDefectConstant n - 1 := by
    simp only [relativeDefectConstant, add_sub_cancel_right]
    positivity
  have hbound : ‖gradient h x‖ ≤ relativeDefectConstant n := by
    have HH' : ‖gradient h x‖ ^ 2 ≤ relativeDefectConstant n - 1 := by
      simpa only [relativeDefectConstant, add_sub_cancel_right] using HH
    nlinarith [sq_nonneg (‖gradient h x‖ - 1), norm_nonneg (gradient h x)]
  rw [hn] at hbound
  exact (div_le_iff₀ (hep x)).mp hbound

theorem diffuseDefect_relative_gradient_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    ‖gradient (diffuseDefect v) x‖ ≤ relativeDefectConstant n * diffuseDefect v x := by
  by_contra! hh
  have hC := relativeDefectConstant_pos n
  let δ := (‖gradient (diffuseDefect v) x‖ - relativeDefectConstant n * diffuseDefect v x) /
    (2 * relativeDefectConstant n)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hh) (by positivity)
  have H := regularized_defect_gradient_bound hv hi hAC hδ x
  have he : relativeDefectConstant n * δ =
      (‖gradient (diffuseDefect v) x‖ - relativeDefectConstant n * diffuseDefect v x) / 2 := by
    dsimp [δ]
    field_simp [hC.ne']
  nlinarith

lemma diffuseDefect_log_lipschitz {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (x y : Space n) :
    |Real.log (diffuseDefect v y) - Real.log (diffuseDefect v x)| ≤
      relativeDefectConstant n * ‖y - x‖ := by
  let h := fun z => Real.log (diffuseDefect v z)
  have hDs := diffuseDefect_smooth hv hi
  have hh : ContDiff ℝ ∞ h := hDs.log (fun z => (hp z).ne')
  have hgrad (z : Space n) : ‖gradient h z‖ ≤ relativeDefectConstant n := by
    dsimp only [h]
    rw [gradient_log (hDs.differentiable (by simp) z) (hp z).ne', norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos (hp z)]
    have H := diffuseDefect_relative_gradient_bound hv hi hAC z
    calc (diffuseDefect v z)⁻¹ * ‖gradient (diffuseDefect v) z‖ ≤
        (diffuseDefect v z)⁻¹ * (relativeDefectConstant n * diffuseDefect v z) :=
          mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (hp z).le)
      _ = relativeDefectConstant n := by field_simp [(hp z).ne']
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (fun z _ => hh.differentiable (by simp) z)
    (fun z _ => show ‖fderiv ℝ h z‖ ≤ relativeDefectConstant n by
      simpa only [gradient, LinearIsometryEquiv.norm_map] using hgrad z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  exact H

lemma diffuseDefect_exp_comparison_crude {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) (x y : Space n) :
    diffuseDefect v y ≤ Real.exp (relativeDefectConstant n * ‖y - x‖) * diffuseDefect v x := by
  have H := (abs_le.mp (diffuseDefect_log_lipschitz hv hi hAC hp x y)).2
  have HH := Real.exp_le_exp.mpr H
  rw [Real.exp_sub, Real.exp_log (hp y), Real.exp_log (hp x)] at HH
  exact (div_le_iff₀ (hp x)).mp HH

lemma coordDeriv_comp_scalar {n : ℕ} {f : Space n → ℝ} {g : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hg : ∀ z, DifferentiableAt ℝ g (f z))
    (i : Fin n) (x : Space n) :
    coordDeriv (fun z => g (f z)) i x = deriv g (f x) * coordDeriv f i x := by
  have H := (hg x).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt
  have He : fderiv ℝ (fun z => g (f z)) x = deriv g (f x) • fderiv ℝ f x := H.fderiv
  simp only [coordDeriv, He, smul_apply, smul_eq_mul]

lemma laplacian_comp_scalar {n : ℕ} {f : Space n → ℝ} {g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 (fun z => g (f z)))
    (hgd : ∀ z, DifferentiableAt ℝ g (f z))
    (hgdd : ∀ z, DifferentiableAt ℝ (deriv g) (f z)) (x : Space n) :
    Laplacian.laplacian (fun z => g (f z)) x =
      deriv (deriv g) (f x) * ‖gradient f x‖ ^ 2 + deriv g (f x) * Laplacian.laplacian f x := by
  have hd := hf.differentiable (by norm_num)
  have hfirst (i : Fin n) : coordDeriv (fun z => g (f z)) i =
      fun z => deriv g (f z) * coordDeriv f i z := by
    funext z; exact coordDeriv_comp_scalar hd hgd i z
  rw [laplacian_eq_sum_coordDeriv hg, laplacian_eq_sum_coordDeriv hf,
    gradient_norm_sq]
  simp_rw [hfirst]
  have hsum (i : Fin n) :
      coordDeriv (fun z => deriv g (f z) * coordDeriv f i z) i x =
      deriv (deriv g) (f x) * coordDeriv f i x ^ 2 +
        deriv g (f x) * coordDeriv (coordDeriv f i) i x := by
    have hdd : Differentiable ℝ (fun z => deriv g (f z)) := fun z => (hgdd z).comp z (hd z)
    rw [coordDeriv_mul hdd ((coordDeriv_contDiff hf i).differentiable (by norm_num)),
      coordDeriv_comp_scalar hd hgdd]
    ring
  simp_rw [hsum]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end DeGiorgi
end

end OAI
