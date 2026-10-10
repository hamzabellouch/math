import OAI.Analysis.AllenCahn.TensorSources

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma diffuse_drift_commute {n : ℕ} {v f r : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hf : ContDiff ℝ ∞ f) (hr : ContDiff ℝ ∞ r)
    (heq : ∀ x, Laplacian.laplacian f x - fderiv ℝ f x (diffuseDrift v x) = r x)
    (k : Fin n) (x : Space n) :
    Laplacian.laplacian (coordDeriv f k) x - fderiv ℝ (coordDeriv f k) x (diffuseDrift v x) =
      coordDeriv r k x + ∑ l : Fin n, coordDeriv (driftCoeff v l) k x * coordDeriv f l x := by
  have hc (l : Fin n) := (tensorCoeff_smooth hv hi).2.2.2.2 l
  have hdc (l : Fin n) := (hc l).differentiable (by simp)
  have hdfl (l : Fin n) := (coordDeriv_smooth hf l).differentiable (by simp)
  have he : Laplacian.laplacian f = fun y => r y + ∑ l : Fin n, driftCoeff v l y * coordDeriv f l y := by
    funext y
    have hh := heq y
    rw [fderiv_diffuseDrift_sum] at hh
    linarith
  rw [laplacian_coordDeriv hf, he, coordDeriv_add (g := fun y => ∑ l : Fin n, driftCoeff v l y * coordDeriv f l y)
    (hr.differentiable (by simp))
    (Differentiable.fun_sum (fun l _ => (hdc l).fun_mul (hdfl l))),
    coordDeriv_sum (f := fun l y => driftCoeff v l y * coordDeriv f l y) _
      (fun l _ => (hdc l).fun_mul (hdfl l)), fderiv_diffuseDrift_sum]
  have hh (l : Fin n) : coordDeriv (fun y => driftCoeff v l y * coordDeriv f l y) k x =
      driftCoeff v l x * coordDeriv (coordDeriv f k) l x +
        coordDeriv (driftCoeff v l) k x * coordDeriv f l x := by
    rw [coordDeriv_mul (hdc l) (hdfl l), coordDeriv_comm (smooth_C2 hf) l k]
    ring
  simp_rw [hh]
  rw [Finset.sum_add_distrib]
  ring

lemma inverseHessian_deriv_drift_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j k : Fin n) (x : Space n) :
    |Laplacian.laplacian (coordDeriv (inverseHessian v i j) k) x -
      fderiv ℝ (coordDeriv (inverseHessian v i j) k) x (diffuseDrift v x)| ≤
      tensorCoeffConstant n * (1 + 6 * n) *
        (diffuseDefect v x + Real.sqrt (hessianSquare v x) + Real.sqrt (tensorDerivativeSquare v x)) := by
  rw [diffuse_drift_commute hv hi (inverseHessian_smooth hv hi i j) (tensorSource_smooth hv hi i j)
    (inverseHessian_drift_factored hv hi hAC i j)]
  let C := tensorCoeffConstant n
  let S := Real.sqrt (hessianSquare v x)
  let Q := Real.sqrt (tensorDerivativeSquare v x)
  have hC : 0 ≤ C := (tensorCoeffConstant_pos n).le
  have hD : 0 ≤ diffuseDefect v x := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hh : |∑ l : Fin n, coordDeriv (driftCoeff v l) k x * coordDeriv (inverseHessian v i j) l x| ≤
      n * (C * Q) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans (Finset.sum_le_sum (fun (l : Fin n) (_ : l ∈ Finset.univ) => show
      |coordDeriv (driftCoeff v l) k x * coordDeriv (inverseHessian v i j) l x| ≤ C * Q by
        rw [abs_mul]
        exact mul_le_mul (((tensorCoeff_C1Bound hv hi hAC).2.2.2.2 l).2 k x)
          (inverseHessian_deriv_abs_le_sqrt v i j l x) (abs_nonneg _) hC))
    simp
  apply ((abs_add_le _ _).trans (add_le_add (tensorSource_coord_bound hv hi hAC i j k x) hh)).trans
  change C * (1 + 5 * n) * (diffuseDefect v x + S + Q) + n * (C * Q) ≤
    C * (1 + 6 * n) * (diffuseDefect v x + S + Q)
  have hpos : 0 ≤ C * n * (diffuseDefect v x + S) := by positivity
  nlinarith

lemma drift_sum_identity {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Space n → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (b : Space n → Space n) (x : Space n) :
    Laplacian.laplacian (fun y => ∑ i ∈ s, f i y) x -
      fderiv ℝ (fun y => ∑ i ∈ s, f i y) x (b x) =
        ∑ i ∈ s, (Laplacian.laplacian (f i) x - fderiv ℝ (f i) x (b x)) := by
  rw [laplacian_sum s hf, fderiv_fun_sum (A := f)
    (fun i hi => (hf i hi).differentiable (by norm_num) x)]
  simp only [sum_apply, Finset.sum_sub_distrib]

lemma tensorDerivativeSquare_eq_sum {n : ℕ} (v : Space n → ℝ) (x : Space n) :
    tensorDerivativeSquare v x = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      coordDeriv (inverseHessian v i j) k x ^ 2 := by
  simp only [tensorDerivativeSquare, gradient_norm_sq]

lemma tensorDerivativeSquare_uniform {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    tensorDerivativeSquare v x ≤ n ^ 3 * inverseJetConstant n ^ 2 := by
  rw [tensorDerivativeSquare_eq_sum]
  have hh (i j k : Fin n) : coordDeriv (inverseHessian v i j) k x ^ 2 ≤ inverseJetConstant n ^ 2 := by
    rw [← sq_abs (coordDeriv (inverseHessian v i j) k x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (((inverseJet_C1Bound hv hi hAC).2.2.2.2 i j).2 k x) 2
  apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    Finset.sum_le_sum (fun k _ => hh i j k)))).trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf; rfl

lemma tensorDerivativeSquare_drift_identity {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (x : Space n) :
    Laplacian.laplacian (tensorDerivativeSquare v) x -
      fderiv ℝ (tensorDerivativeSquare v) x (diffuseDrift v x) =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (2 * ‖gradient (coordDeriv (inverseHessian v i j) k) x‖ ^ 2 +
        2 * coordDeriv (inverseHessian v i j) k x *
          (Laplacian.laplacian (coordDeriv (inverseHessian v i j) k) x -
            fderiv ℝ (coordDeriv (inverseHessian v i j) k) x (diffuseDrift v x))) := by
  have hT (i j k : Fin n) := smooth_C2 (coordDeriv_smooth (inverseHessian_smooth hv hi i j) k)
  have he : tensorDerivativeSquare v = fun y => ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      coordDeriv (inverseHessian v i j) k y ^ 2 := funext (tensorDerivativeSquare_eq_sum v)
  rw [he, drift_sum_identity _ (fun i _ => ContDiff.sum (fun j _ =>
    ContDiff.sum (fun k _ => (hT i j k).pow 2)))]
  apply Finset.sum_congr rfl; intro i _
  rw [drift_sum_identity _ (fun j _ => ContDiff.sum (fun k _ => (hT i j k).pow 2))]
  apply Finset.sum_congr rfl; intro j _
  rw [drift_sum_identity _ (fun k _ => (hT i j k).pow 2)]
  apply Finset.sum_congr rfl; intro k _
  exact drift_square_identity (hT i j k) (diffuseDrift v) x

def tensorSecondBernsteinConstant (n : ℕ) : ℝ :=
  1 + 3 * n ^ 3 * (tensorCoeffConstant n * (1 + 6 * n)) ^ 2 * (tensorBernsteinConstant n + 4)

lemma tensorSecondBernsteinConstant_pos (n : ℕ) : 0 < tensorSecondBernsteinConstant n := by
  dsimp [tensorSecondBernsteinConstant, tensorBernsteinConstant]; positivity

lemma tensorDerivativeSquare_drift_lower {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    -tensorSecondBernsteinConstant n * (tensorDerivativeSquare v x + diffuseDefect v x) ≤
      Laplacian.laplacian (tensorDerivativeSquare v) x -
        fderiv ℝ (tensorDerivativeSquare v) x (diffuseDrift v x) := by
  let C := tensorCoeffConstant n * (1 + 6 * n)
  let S := Real.sqrt (hessianSquare v x)
  let Q := Real.sqrt (tensorDerivativeSquare v x)
  have hC : 0 ≤ C := mul_nonneg (tensorCoeffConstant_pos n).le (by positivity)
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hD1 := diffuseDefect_le_one v x
  have hD2 : diffuseDefect v x ^ 2 ≤ diffuseDefect v x := by nlinarith
  have hS : S ^ 2 = hessianSquare v x := Real.sq_sqrt (hessianSquare_nonneg v x)
  have hQ : Q ^ 2 = tensorDerivativeSquare v x := Real.sq_sqrt (tensorDerivativeSquare_nonneg v x)
  have hBs : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  have hpair (i j k : Fin n) :
      -(coordDeriv (inverseHessian v i j) k x ^ 2) -
        3 * C ^ 2 * (diffuseDefect v x + hessianSquare v x + tensorDerivativeSquare v x) ≤
      2 * ‖gradient (coordDeriv (inverseHessian v i j) k) x‖ ^ 2 +
        2 * coordDeriv (inverseHessian v i j) k x *
          (Laplacian.laplacian (coordDeriv (inverseHessian v i j) k) x -
            fderiv ℝ (coordDeriv (inverseHessian v i j) k) x (diffuseDrift v x)) := by
    let R := Laplacian.laplacian (coordDeriv (inverseHessian v i j) k) x -
      fderiv ℝ (coordDeriv (inverseHessian v i j) k) x (diffuseDrift v x)
    have hR : |R| ≤ C * (diffuseDefect v x + S + Q) := inverseHessian_deriv_drift_bound hv hi hAC i j k x
    have hR2 : R ^ 2 ≤ 3 * C ^ 2 *
        (diffuseDefect v x + hessianSquare v x + tensorDerivativeSquare v x) := by
      calc R ^ 2 = |R| ^ 2 := (sq_abs R).symm
        _ ≤ (C * (diffuseDefect v x + S + Q)) ^ 2 := pow_le_pow_left₀ (abs_nonneg R) hR 2
        _ = C ^ 2 * (diffuseDefect v x + S + Q) ^ 2 := by ring
        _ ≤ C ^ 2 * (3 * (diffuseDefect v x + hessianSquare v x + tensorDerivativeSquare v x)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
          nlinarith [sq_nonneg (diffuseDefect v x - S), sq_nonneg (diffuseDefect v x - Q), sq_nonneg (S - Q)]
        _ = _ := by ring
    have hy := sq_nonneg (coordDeriv (inverseHessian v i j) k x + R)
    have hg := sq_nonneg ‖gradient (coordDeriv (inverseHessian v i j) k) x‖
    change _ ≤ 2 * ‖gradient (coordDeriv (inverseHessian v i j) k) x‖ ^ 2 +
      2 * coordDeriv (inverseHessian v i j) k x * R
    nlinarith
  rw [tensorDerivativeSquare_drift_identity hv hi]
  have hsum := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (j : Fin n) (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum (fun (k : Fin n) (_ : k ∈ Finset.univ) => hpair i j k)))
  apply le_trans _ hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← tensorDerivativeSquare_eq_sum]
  have hFD := hessianSquare_le_defect hv hi hAC x
  have hE := tensorDerivativeSquare_nonneg v x
  have hbig : diffuseDefect v x + hessianSquare v x + tensorDerivativeSquare v x ≤
      (tensorBernsteinConstant n + 4) * (diffuseDefect v x + tensorDerivativeSquare v x) := by
    nlinarith [mul_nonneg hBs hE]
  have hscale := mul_le_mul_of_nonneg_left hbig (show 0 ≤ 3 * (n : ℝ) ^ 3 * C ^ 2 by positivity)
  dsimp only [tensorSecondBernsteinConstant]
  change -(1 + 3 * (n : ℝ) ^ 3 * C ^ 2 * (tensorBernsteinConstant n + 4)) * _ ≤ _
  nlinarith

lemma hessianSquare_drift_lower_refined {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    2 * tensorDerivativeSquare v x - tensorBernsteinConstant n * (hessianSquare v x + diffuseDefect v x ^ 2) ≤
      Laplacian.laplacian (hessianSquare v) x - fderiv ℝ (hessianSquare v) x (diffuseDrift v x) := by
  let C := tensorSystemConstant n
  let S := Real.sqrt (hessianSquare v x)
  have hC : 0 ≤ C := by dsimp [C, tensorSystemConstant]; positivity
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = hessianSquare v x := Real.sq_sqrt (hessianSquare_nonneg v x)
  have hD : 0 ≤ diffuseDefect v x := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hpair (i j : Fin n) :
      2 * ‖gradient (inverseHessian v i j) x‖ ^ 2 - (inverseHessian v i j x ^ 2) - 2 * C ^ 2 * (hessianSquare v x + diffuseDefect v x ^ 2) ≤
        2 * ‖gradient (inverseHessian v i j) x‖ ^ 2 +
        2 * inverseHessian v i j x * (Laplacian.laplacian (inverseHessian v i j) x -
          fderiv ℝ (inverseHessian v i j) x (diffuseDrift v x)) := by
    let R := Laplacian.laplacian (inverseHessian v i j) x - fderiv ℝ (inverseHessian v i j) x (diffuseDrift v x)
    have hR : |R| ≤ C * (diffuseDefect v x + S) := inverseHessian_drift_abs_bound hv hi hAC i j x
    have hR2 : R ^ 2 ≤ 2 * C ^ 2 * (hessianSquare v x + diffuseDefect v x ^ 2) := by
      calc R ^ 2 = |R| ^ 2 := (sq_abs R).symm
        _ ≤ (C * (diffuseDefect v x + S)) ^ 2 := pow_le_pow_left₀ (abs_nonneg R) hR 2
        _ = C ^ 2 * (diffuseDefect v x + S) ^ 2 := by ring
        _ ≤ C ^ 2 * (2 * (hessianSquare v x + diffuseDefect v x ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
          nlinarith [sq_nonneg (diffuseDefect v x - S)]
        _ = _ := by ring
    have hy := sq_nonneg (inverseHessian v i j x + R)
    have hg := sq_nonneg ‖gradient (inverseHessian v i j) x‖
    change _ ≤ 2 * ‖gradient (inverseHessian v i j) x‖ ^ 2 + 2 * inverseHessian v i j x * R
    nlinarith
  rw [hessianSquare_drift_identity hv hi]
  have hsum := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (j : Fin n) (_ : j ∈ Finset.univ) => hpair i j))
  apply le_trans _ hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← hessianSquare_eq_sum]
  change 2 * tensorDerivativeSquare v x - tensorBernsteinConstant n * _ ≤
    2 * tensorDerivativeSquare v x - hessianSquare v x - _
  dsimp only [tensorBernsteinConstant]
  change 2 * tensorDerivativeSquare v x - (1 + 2 * (n : ℝ) ^ 2 * C ^ 2) * _ ≤ _
  nlinarith [sq_nonneg (diffuseDefect v x)]

def carrierScale (n : ℕ) : ℝ := 2 * (tensorBernsteinConstant n + 3) + 1

def defectCarrier {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  diffuseDefect v x - hessianSquare v x / carrierScale n

lemma carrierScale_pos (n : ℕ) : 0 < carrierScale n := by
  dsimp [carrierScale, tensorBernsteinConstant]; positivity

lemma defectCarrier_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (defectCarrier v) := (diffuseDefect_smooth hv hi).sub
      ((hessianSquare_smooth hv hi).div_const _)

lemma defectCarrier_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) : diffuseDefect v x / 2 ≤ defectCarrier v x ∧ defectCarrier v x ≤ diffuseDefect v x := by
  have hF := hessianSquare_le_defect hv hi hAC x
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hscale := carrierScale_pos n
  have hFp := hessianSquare_nonneg v x
  have hquot : hessianSquare v x / carrierScale n ≤ diffuseDefect v x / 2 := by
    apply (div_le_iff₀ hscale).mpr
    dsimp [carrierScale]
    nlinarith
  dsimp [defectCarrier]
  exact ⟨by linarith, sub_le_self _ (div_nonneg hFp hscale.le)⟩

lemma drift_const_mul {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (b : Space n → Space n) (c : ℝ) (x : Space n) :
    Laplacian.laplacian (fun y => c * f y) x - fderiv ℝ (fun y => c * f y) x (b x) =
      c * (Laplacian.laplacian f x - fderiv ℝ f x (b x)) := by
  rw [laplacian_fun_const_mul hf]
  rw [fderiv_const_mul (hf.differentiable (by norm_num) x)]
  simp only [smul_apply, smul_eq_mul]; ring

lemma drift_sub {n : ℕ} {f g : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (b : Space n → Space n) (x : Space n) :
    Laplacian.laplacian (fun y => f y - g y) x - fderiv ℝ (fun y => f y - g y) x (b x) =
      (Laplacian.laplacian f x - fderiv ℝ f x (b x)) -
        (Laplacian.laplacian g x - fderiv ℝ g x (b x)) := by
  rw [laplacian_fun_sub hf hg, fderiv_fun_sub (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)]
  simp only [sub_apply]; ring

lemma defectCarrier_drift_upper {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    Laplacian.laplacian (defectCarrier v) x - fderiv ℝ (defectCarrier v) x (diffuseDrift v x) ≤
      2 * (2 + tensorBernsteinConstant n * (tensorBernsteinConstant n + 4) / carrierScale n) *
        defectCarrier v x - 2 * (tensorDerivativeSquare v x / carrierScale n) := by
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hD1 := diffuseDefect_le_one v x
  have hD2 : diffuseDefect v x ^ 2 ≤ diffuseDefect v x := by nlinarith
  have hF := hessianSquare_le_defect hv hi hAC x
  have hF0 := hessianSquare_nonneg v x
  have hBs : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  have hs := carrierScale_pos n
  have hCD := (defectCarrier_bounds hv hi hAC x).1
  have hUp := diffuseDefect_drift_upper hv hi hAC x
  have hLow := hessianSquare_drift_lower_refined hv hi hAC x
  have hlow' := div_le_div_of_nonneg_right hLow hs.le
  have hFd : hessianSquare v x + diffuseDefect v x ^ 2 ≤
      (tensorBernsteinConstant n + 4) * diffuseDefect v x := by linarith
  have hFd' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFd hBs) hs.le
  have hCD' := mul_le_mul_of_nonneg_left hCD
    (show 0 ≤ 2 * (2 + tensorBernsteinConstant n * (tensorBernsteinConstant n + 4) / carrierScale n) by positivity)
  have he : defectCarrier v = fun y => diffuseDefect v y -
      (carrierScale n)⁻¹ * hessianSquare v y := by funext y; simp [defectCarrier, div_eq_mul_inv, mul_comm]
  rw [he, drift_sub (smooth_C2 (diffuseDefect_smooth hv hi))
    (contDiff_const.mul (smooth_C2 (hessianSquare_smooth hv hi))),
    drift_const_mul (smooth_C2 (hessianSquare_smooth hv hi))]
  rw [he] at hCD'
  simp only [div_eq_mul_inv] at hlow' hFd' hCD' ⊢
  nlinarith

lemma C1Bound.sub {n : ℕ} {f g : Space n → ℝ} {C K : ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h : C1Bound f C) (h' : C1Bound g K) :
    C1Bound (fun x => f x - g x) (C + K) := by
  constructor
  · intro x; exact (abs_sub (f x) (g x)).trans (add_le_add (h.1 x) (h'.1 x))
  · intro i x
    change |fderiv ℝ (fun y => f y - g y) x (basis n i)| ≤ _
    rw [fderiv_fun_sub (hf x) (hg x), sub_apply]
    exact (abs_sub _ _).trans (add_le_add (h.2 i x) (h'.2 i x))

lemma C1Bound.sum {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Space n → ℝ} {C : ι → ℝ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (h : ∀ i ∈ s, C1Bound (f i) (C i)) :
    C1Bound (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, C i) := by
  constructor
  · intro x; exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => (h i hi).1 x))
  · intro k x
    rw [coordDeriv_sum s hf]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => (h i hi).2 k x))

lemma C1Bound.gradient_bound {n : ℕ} {f : Space n → ℝ} {C : ℝ} (h : C1Bound f C) (x : Space n) :
    ‖gradient f x‖ ≤ n * C := by
  apply (gradient_norm_le_sum_abs f x).trans
  exact (Finset.sum_le_sum (fun k _ => h.2 k x)).trans_eq (by simp)

lemma hessianSquare_C1Bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v) :
    C1Bound (hessianSquare v) (2 * n ^ 2 * inverseJetConstant n ^ 2) := by
  have hJ : 0 ≤ inverseJetConstant n := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseJetConstant_one_le n)
  have hT (i j : Fin n) := (inverseHessian_smooth hv hi i j).differentiable (by simp)
  have hb (i j : Fin n) := (inverseJet_C1Bound hv hi hAC).2.2.2.2 i j
  have hp (i j : Fin n) := (hb i j).mul (hT i j) (hT i j) hJ hJ (hb i j)
  have hh := C1Bound.sum Finset.univ
    (fun i _ => Differentiable.fun_sum (fun j _ => (hT i j).fun_mul (hT i j)))
    (fun i _ => C1Bound.sum Finset.univ (fun j _ => (hT i j).fun_mul (hT i j)) (fun j _ => hp i j))
  have he : (fun y => ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j y * inverseHessian v i j y) =
      hessianSquare v := by funext y; simp only [← pow_two, ← hessianSquare_eq_sum]
  rw [he] at hh
  convert hh using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma defectCarrier_gradient_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    ‖gradient (defectCarrier v) x‖ ≤
      n * (inverseJetConstant n + (carrierScale n)⁻¹ * (2 * n ^ 2 * inverseJetConstant n ^ 2)) := by
  have hF := hessianSquare_C1Bound hv hi hAC
  have hD := (inverseJet_C1Bound hv hi hAC).2.2.1
  have hdF := (hessianSquare_smooth hv hi).differentiable (by simp)
  have hdD := (diffuseDefect_smooth hv hi).differentiable (by simp)
  have hh := hD.sub hdD (hdF.const_mul _) (hF.const_mul hdF (by positivity) (carrierScale n)⁻¹)
  have he : (fun y => diffuseDefect v y - (carrierScale n)⁻¹ * hessianSquare v y) = defectCarrier v := by
    funext y; simp [defectCarrier, div_eq_mul_inv, mul_comm]
  rw [he, abs_of_pos (inv_pos.mpr (carrierScale_pos n))] at hh
  exact hh.gradient_bound x

end DeGiorgi
end

end OAI
