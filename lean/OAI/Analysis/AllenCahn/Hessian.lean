import OAI.Analysis.AllenCahn.DefectCalculus
import OAI.Analysis.AllenCahn.DriftBounds

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff

def diffuseDrift {n : ℕ} (v : Space n → ℝ) (x : Space n) : Space n :=
  (2 * Real.sqrt 2 * v x) • gradient (inverseProfile v) x

def inverseHessian {n : ℕ} (v : Space n → ℝ) (i j : Fin n) : Space n → ℝ :=
  coordDeriv (coordDeriv (inverseProfile v) i) j

def hessianSquare {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ‖gradient (coordDeriv (inverseProfile v) i) x‖ ^ 2

lemma coordDeriv_sub {n : ℕ} {f g : Space n → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => f y - g y) i x = coordDeriv f i x - coordDeriv g i x := by
  simp only [coordDeriv, fderiv_fun_sub (hf x) (hg x), sub_apply]

lemma coordDeriv_abs_le_gradient {n : ℕ} (f : Space n → ℝ) (i : Fin n) (x : Space n) :
    |coordDeriv f i x| ≤ ‖gradient f x‖ := by
  dsimp only [coordDeriv]
  rw [← toDual_gradient]
  change |inner ℝ (gradient f x) (basis n i)| ≤ _
  simpa only [OrthonormalBasis.norm_eq_one, mul_one] using abs_real_inner_le_norm (gradient f x) (basis n i)

lemma coordDeriv_diffuseDefect {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (i : Fin n) (x : Space n) :
    coordDeriv (diffuseDefect v) i x =
      -2 * fderiv ℝ (coordDeriv (inverseProfile v) i) x (gradient (inverseProfile v) x) := by
  have hU := inverseProfile_smooth hv hi
  have hds (j : Fin n) := (coordDeriv_smooth hU j).differentiable (by simp)
  have he : diffuseDefect v = fun y => 1 - ∑ j : Fin n, coordDeriv (inverseProfile v) j y ^ 2 := by
    funext y
    rw [diffuseDefect, gradient_norm_sq]
  rw [he, coordDeriv_sub (g := fun y => ∑ j : Fin n, coordDeriv (inverseProfile v) j y ^ 2)
    (differentiable_const 1) (Differentiable.fun_sum (fun j _ => (hds j).pow 2))]
  have hc : coordDeriv (fun _ : Space n => (1 : ℝ)) i x = 0 := by simp [coordDeriv]
  rw [hc, zero_sub, coordDeriv_sum (f := fun j y => coordDeriv (inverseProfile v) j y ^ 2) _ (fun j _ => (hds j).pow 2)]
  rw [← inner_gradient_left, inner_gradient_eq_sum]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hs : coordDeriv (fun y => coordDeriv (inverseProfile v) j y ^ 2) i x =
      2 * coordDeriv (inverseProfile v) j x * coordDeriv (coordDeriv (inverseProfile v) j) i x := by
    change fderiv ℝ (fun y => coordDeriv (inverseProfile v) j y ^ 2) x (basis n i) = _
    rw [fderiv_fun_pow 2 (hds j x)]
    simp [coordDeriv, mul_assoc]
  rw [hs, coordDeriv_comm (smooth_C2 hU) j i]
  ring

lemma inverseGradient_drift_equation {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i : Fin n) (x : Space n) :
    Laplacian.laplacian (coordDeriv (inverseProfile v) i) x -
      fderiv ℝ (coordDeriv (inverseProfile v) i) x (diffuseDrift v x) =
      -defectWeight v x * diffuseDefect v x * coordDeriv (inverseProfile v) i x := by
  have hU := inverseProfile_smooth hv hi
  have hdv := hv.differentiable (by simp)
  have hD := (diffuseDefect_smooth hv hi).differentiable (by simp)
  have he : Laplacian.laplacian (inverseProfile v) = fun y => -Real.sqrt 2 * v y * diffuseDefect v y :=
    funext (inverseProfile_laplacian_eq (smooth_C2 hv) hi hAC)
  rw [laplacian_coordDeriv hU, he, coordDeriv_mul (hdv.const_mul _) hD]
  have hh : coordDeriv (fun y => -Real.sqrt 2 * v y) i x = -Real.sqrt 2 * coordDeriv v i x := by
    simp [coordDeriv, fderiv_const_mul (hdv x)]
  rw [hh, coordDeriv_profile hdv hi, coordDeriv_diffuseDefect hv hi]
  dsimp only [diffuseDrift]
  rw [map_smul, smul_eq_mul]
  have hsq : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  ring

lemma inverseGradient_uniform_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i : Fin n) (x : Space n) :
    ‖gradient (coordDeriv (inverseProfile v) i) x‖ ≤ 12 * (2 * Real.sqrt 2 + 1) := by
  have hU := inverseProfile_smooth hv hi
  have hp (z : Space n) : |coordDeriv (inverseProfile v) i z| ≤ 1 :=
    (coordDeriv_abs_le_gradient _ _ _).trans (inverseProfile_gradient_bound (smooth_C2 hv) hi hAC z)
  have hde (z : Space n) : |Laplacian.laplacian (coordDeriv (inverseProfile v) i) z -
      fderiv ℝ (coordDeriv (inverseProfile v) i) z (diffuseDrift v z)| ≤ 1 := by
    rw [inverseGradient_drift_equation hv hi hAC, abs_mul, abs_mul, abs_neg]
    have hq : |defectWeight v z| ≤ 1 := by
      change |1 - v z ^ 2| ≤ 1
      rw [abs_of_pos (weight_pos (hi z))]
      nlinarith [sq_nonneg (v z)]
    have hD : |diffuseDefect v z| ≤ 1 := by
      rw [abs_of_nonneg (diffuseDefect_nonneg (smooth_C2 hv) hi hAC z)]
      dsimp [diffuseDefect]
      nlinarith [sq_nonneg ‖gradient (inverseProfile v) z‖]
    calc |defectWeight v z| * |diffuseDefect v z| * |coordDeriv (inverseProfile v) i z| ≤ 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul hq hD (abs_nonneg _) (by norm_num)) (hp z) (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  convert PoissonSupport.DeGiorgi.bounded_drift_gradient
    (smooth_C2 (coordDeriv_smooth hU i)) (diffuseDrift v)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ 2 * Real.sqrt 2) hp
    (diffuseDrift_bound (smooth_C2 hv) hi hAC) hde x using 1
  norm_num

lemma hessianSquare_uniform_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    hessianSquare v x ≤ n * (12 * (2 * Real.sqrt 2 + 1)) ^ 2 := by
  calc ∑ i : Fin n, ‖gradient (coordDeriv (inverseProfile v) i) x‖ ^ 2 ≤
      ∑ _i : Fin n, (12 * (2 * Real.sqrt 2 + 1)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh := inverseGradient_uniform_bound hv hi hAC i x
        have hh0 := norm_nonneg (gradient (coordDeriv (inverseProfile v) i) x)
        nlinarith
       _ = _ := by simp

lemma inverseHessian_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (i j : Fin n) :
    ContDiff ℝ ∞ (inverseHessian v i j) :=
  coordDeriv_smooth (coordDeriv_smooth (inverseProfile_smooth hv hi) i) j

lemma inverseHessian_symm {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (i j : Fin n) :
    inverseHessian v i j = inverseHessian v j i :=
  coordDeriv_comm (smooth_C2 (inverseProfile_smooth hv hi)) i j

lemma hessianSquare_nonneg {n : ℕ} (v : Space n → ℝ) (x : Space n) :
    0 ≤ hessianSquare v x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma hessianSquare_eq_sum {n : ℕ} (v : Space n → ℝ) (x : Space n) :
    hessianSquare v x = ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j x ^ 2 := by
  simp only [hessianSquare, gradient_norm_sq, inverseHessian]

lemma hessianSquare_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (hessianSquare v) := by
  have he : hessianSquare v = fun x => ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j x ^ 2 :=
    funext (hessianSquare_eq_sum v)
  rw [he]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (inverseHessian_smooth hv hi i j).pow 2))

lemma inverseHessian_sq_le {n : ℕ} (v : Space n → ℝ) (i j : Fin n) (x : Space n) :
    inverseHessian v i j x ^ 2 ≤ hessianSquare v x := by
  rw [hessianSquare_eq_sum]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (inverseHessian v i k x)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg
      (fun b _ => sq_nonneg (inverseHessian v a b x))) (Finset.mem_univ i))

lemma inverseHessian_abs_le {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j : Fin n) (x : Space n) :
    |inverseHessian v i j x| ≤ 12 * (2 * Real.sqrt 2 + 1) :=
  (coordDeriv_abs_le_gradient _ _ _).trans (inverseGradient_uniform_bound hv hi hAC i x)

lemma fderiv_diffuseDrift {n : ℕ} (v f : Space n → ℝ) (x : Space n) :
    fderiv ℝ f x (diffuseDrift v x) =
      2 * Real.sqrt 2 * v x * (∑ k : Fin n, coordDeriv (inverseProfile v) k x * coordDeriv f k x) := by
  rw [diffuseDrift, map_smul, smul_eq_mul, ← inner_gradient_left, real_inner_comm,
    inner_gradient_eq_sum]

lemma coordDeriv_diffuseDefect_sum {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (i : Fin n) (x : Space n) :
    coordDeriv (diffuseDefect v) i x =
      -2 * ∑ k : Fin n, coordDeriv (inverseProfile v) k x * inverseHessian v i k x := by
  rw [coordDeriv_diffuseDefect hv hi, ← inner_gradient_left, real_inner_comm,
    inner_gradient_eq_sum]
  rfl

lemma coordDeriv_defectWeight {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (i : Fin n) (x : Space n) :
    coordDeriv (defectWeight v) i x =
      -Real.sqrt 2 * v x * defectWeight v x * coordDeriv (inverseProfile v) i x := by
  have hdv := hv.differentiable (by simp)
  have he : coordDeriv (defectWeight v) i x = -2 * v x * coordDeriv v i x := by
    change fderiv ℝ (fun y => 1 - v y ^ 2) x (basis n i) =
      -2 * v x * fderiv ℝ v x (basis n i)
    rw [fderiv_fun_sub (g := fun y => v y ^ 2) (differentiableAt_const 1) ((hdv x).pow 2)]
    simp [fderiv_fun_pow 2 (hdv x), mul_assoc]
  rw [he, coordDeriv_profile hdv hi]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma inverseHessian_drift_system {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j : Fin n) (x : Space n) :
    Laplacian.laplacian (inverseHessian v i j) x -
      fderiv ℝ (inverseHessian v i j) x (diffuseDrift v x) =
    -defectWeight v x * diffuseDefect v x * inverseHessian v i j x +
      Real.sqrt 2 * v x * defectWeight v x * diffuseDefect v x *
        coordDeriv (inverseProfile v) i x * coordDeriv (inverseProfile v) j x -
      defectWeight v x * (coordDeriv (inverseProfile v) i x * coordDeriv (diffuseDefect v) j x +
        coordDeriv (inverseProfile v) j x * coordDeriv (diffuseDefect v) i x) +
      2 * Real.sqrt 2 * v x *
        (∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x) := by
  have hU := inverseProfile_smooth hv hi
  have hp (k : Fin n) := coordDeriv_smooth hU k
  have hT (k l : Fin n) := inverseHessian_smooth hv hi k l
  have hD := diffuseDefect_smooth hv hi
  have hq : ContDiff ℝ ∞ (defectWeight v) := contDiff_const.sub (hv.pow 2)
  have hc : ContDiff ℝ ∞ (fun y => 2 * Real.sqrt 2 * v y) := contDiff_const.mul hv
  have hS : ContDiff ℝ ∞ (fun y => ∑ k : Fin n,
      coordDeriv (inverseProfile v) k y * inverseHessian v i k y) :=
    ContDiff.sum (fun k _ => (hp k).mul (hT i k))
  have he : Laplacian.laplacian (coordDeriv (inverseProfile v) i) = fun y =>
      2 * Real.sqrt 2 * v y * (∑ k : Fin n, coordDeriv (inverseProfile v) k y * inverseHessian v i k y) -
      defectWeight v y * diffuseDefect v y * coordDeriv (inverseProfile v) i y := by
    funext y
    have hh := inverseGradient_drift_equation hv hi hAC i y
    rw [fderiv_diffuseDrift] at hh
    dsimp only [inverseHessian]
    linarith
  have hcl : coordDeriv (fun y => 2 * Real.sqrt 2 * v y) j x =
      2 * defectWeight v x * coordDeriv (inverseProfile v) j x := by
    have hh : coordDeriv (fun y => 2 * Real.sqrt 2 * v y) j x =
        2 * Real.sqrt 2 * coordDeriv v j x := by
      simp [coordDeriv, fderiv_const_mul (hv.differentiable (by simp) x)]
    rw [hh, coordDeriv_profile (hv.differentiable (by simp)) hi]
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp
  have hSl : coordDeriv (fun y => ∑ k : Fin n,
      coordDeriv (inverseProfile v) k y * inverseHessian v i k y) j x =
      (∑ k : Fin n, inverseHessian v k j x * inverseHessian v i k x) +
        (∑ k : Fin n, coordDeriv (inverseProfile v) k x * coordDeriv (inverseHessian v i j) k x) := by
    rw [coordDeriv_sum _ (fun k _ => ((hp k).mul (hT i k)).differentiable (by simp))]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [coordDeriv_mul ((hp k).differentiable (by simp)) ((hT i k).differentiable (by simp))]
    rw [show coordDeriv (inverseHessian v i k) j = coordDeriv (inverseHessian v i j) k from
      coordDeriv_comm (smooth_C2 (hp i)) k j]
    simp only [inverseHessian]
    ring
  change Laplacian.laplacian (coordDeriv (coordDeriv (inverseProfile v) i) j) x - _ = _
  rw [laplacian_coordDeriv (hp i), he,
    coordDeriv_sub ((hc.mul hS).differentiable (by simp))
      (((hq.mul hD).mul (hp i)).differentiable (by simp))]
  rw [coordDeriv_mul (hc.differentiable (by simp)) (hS.differentiable (by simp)), hcl, hSl,
      coordDeriv_mul ((hq.mul hD).differentiable (by simp)) ((hp i).differentiable (by simp)),
      coordDeriv_mul (hq.differentiable (by simp)) (hD.differentiable (by simp)),
      coordDeriv_defectWeight hv hi, fderiv_diffuseDrift]
  rw [coordDeriv_diffuseDefect_sum hv hi i]
  have hflip : ∑ k : Fin n, inverseHessian v k j x * inverseHessian v i k x =
      ∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hflip]
  change _ = _
  dsimp only [inverseHessian]
  ring

lemma diffuseDefect_le_one {n : ℕ} (v : Space n → ℝ) (x : Space n) :
    diffuseDefect v x ≤ 1 := by
  dsimp [diffuseDefect]
  nlinarith [sq_nonneg ‖gradient (inverseProfile v) x‖]

lemma inverseHessian_abs_le_sqrt {n : ℕ} (v : Space n → ℝ) (i j : Fin n) (x : Space n) :
    |inverseHessian v i j x| ≤ Real.sqrt (hessianSquare v x) := by
  have hs := Real.sq_sqrt (hessianSquare_nonneg v x)
  have hh := inverseHessian_sq_le v i j x
  nlinarith [Real.sqrt_nonneg (hessianSquare v x), sq_abs (inverseHessian v i j x)]

lemma coordDeriv_diffuseDefect_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i : Fin n) (x : Space n) :
    |coordDeriv (diffuseDefect v) i x| ≤ 2 * n * Real.sqrt (hessianSquare v x) := by
  rw [coordDeriv_diffuseDefect_sum hv hi, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |∑ k : Fin n, coordDeriv (inverseProfile v) k x * inverseHessian v i k x| ≤
      2 * ∑ k : Fin n, |coordDeriv (inverseProfile v) k x * inverseHessian v i k x| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ _k : Fin n, Real.sqrt (hessianSquare v x) := by
      gcongr with k
      rw [abs_mul]
      have hp : |coordDeriv (inverseProfile v) k x| ≤ 1 :=
        (coordDeriv_abs_le_gradient _ _ _).trans (inverseProfile_gradient_bound (smooth_C2 hv) hi hAC x)
      simpa only [one_mul] using mul_le_mul hp (inverseHessian_abs_le_sqrt v i k x)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp; ring

lemma coordDeriv_diffuseDefect_uniform_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i : Fin n) (x : Space n) :
    |coordDeriv (diffuseDefect v) i x| ≤ 2 * n * (12 * (2 * Real.sqrt 2 + 1)) := by
  rw [coordDeriv_diffuseDefect_sum hv hi, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |∑ k : Fin n, coordDeriv (inverseProfile v) k x * inverseHessian v i k x| ≤
      2 * ∑ k : Fin n, |coordDeriv (inverseProfile v) k x * inverseHessian v i k x| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ _k : Fin n, (12 * (2 * Real.sqrt 2 + 1)) := by
      gcongr with k
      rw [abs_mul]
      have hp : |coordDeriv (inverseProfile v) k x| ≤ 1 :=
        (coordDeriv_abs_le_gradient _ _ _).trans (inverseProfile_gradient_bound (smooth_C2 hv) hi hAC x)
      simpa only [one_mul] using mul_le_mul hp (inverseHessian_abs_le hv hi hAC i k x)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp; ring

lemma gradient_norm_le_sum_abs {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖gradient f x‖ ≤ ∑ i : Fin n, |coordDeriv f i x| := by
  nth_rw 1 [← (basis n).sum_repr' (gradient f x)]
  calc ‖∑ i : Fin n, inner ℝ (basis n i) (gradient f x) • basis n i‖ ≤
      ∑ i : Fin n, ‖inner ℝ (basis n i) (gradient f x) • basis n i‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one,
        real_inner_comm, inner_gradient_left, coordDeriv]

lemma diffuseDefect_gradient_uniform_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) : ‖gradient (diffuseDefect v) x‖ ≤ 2 * n ^ 2 * (12 * (2 * Real.sqrt 2 + 1)) := by
  calc ‖gradient (diffuseDefect v) x‖ ≤ ∑ i : Fin n, |coordDeriv (diffuseDefect v) i x| :=
      gradient_norm_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * n * (12 * (2 * Real.sqrt 2 + 1)) :=
      Finset.sum_le_sum (fun i _ => coordDeriv_diffuseDefect_uniform_bound hv hi hAC i x)
    _ = _ := by simp; ring

end DeGiorgi
end

end OAI
