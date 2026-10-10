import OAI.Analysis.AllenCahn.Bernstein

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

def derivativeDefectConstant (n : ℕ) : ℝ :=
  carrierScale n * (2 * tensorSecondBernsteinConstant n +
    2 * (2 + tensorBernsteinConstant n * (tensorBernsteinConstant n + 4) / carrierScale n) + 1)

lemma derivativeDefectConstant_pos (n : ℕ) : 0 < derivativeDefectConstant n := by
  have hB : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  have hA := tensorSecondBernsteinConstant_pos n
  have hs := carrierScale_pos n
  dsimp [derivativeDefectConstant]; positivity

theorem tensorDerivativeSquare_le_defect {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) : tensorDerivativeSquare v x ≤ derivativeDefectConstant n * diffuseDefect v x := by
  let a := carrierScale n
  let f := fun y => tensorDerivativeSquare v y / a
  let c := 2 * (2 + tensorBernsteinConstant n * (tensorBernsteinConstant n + 4) / a)
  have ha : 0 < a := carrierScale_pos n
  have ha1 : 1 ≤ a := by
    have hh : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
    dsimp [a, carrierScale]; linarith
  have hA := tensorSecondBernsteinConstant_pos n
  have hB : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  have hJ : 0 ≤ inverseJetConstant n := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseJetConstant_one_le n)
  have hf : ContDiff ℝ 2 f := (smooth_C2 (tensorDerivativeSquare_smooth hv hi)).div_const _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hfde (y : Space n) : - (2 * tensorSecondBernsteinConstant n) * (f y + defectCarrier v y) ≤
      Laplacian.laplacian f y - fderiv ℝ f y (diffuseDrift v y) := by
    have hLow := div_le_div_of_nonneg_right (tensorDerivativeSquare_drift_lower hv hi hAC y) ha.le
    have hE := tensorDerivativeSquare_nonneg v y
    have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC y
    have hP := (defectCarrier_bounds hv hi hAC y).1
    have hP0 : 0 ≤ defectCarrier v y := (div_nonneg hD (by norm_num)).trans hP
    have hDdiv : diffuseDefect v y / a ≤ 2 * defectCarrier v y := by
      apply (div_le_iff₀ ha).mpr
      nlinarith [mul_nonneg hP0 (sub_nonneg.mpr ha1)]
    have hEdiv : 0 ≤ tensorDerivativeSquare v y / a := div_nonneg hE ha.le
    have hscale := mul_le_mul_of_nonneg_left hDdiv hA.le
    have he : f = fun z => a⁻¹ * tensorDerivativeSquare v z := by
      funext z; dsimp [f]; rw [div_eq_mul_inv, mul_comm]
    rw [he, drift_const_mul (smooth_C2 (tensorDerivativeSquare_smooth hv hi))]
    dsimp only [f] at *
    simp only [div_eq_mul_inv] at hLow hscale hEdiv ⊢
    nlinarith
  have HH := quotient_bernstein_linear hf (smooth_C2 (defectCarrier_smooth hv hi)) (diffuseDrift v)
    (M := n ^ 3 * inverseJetConstant n ^ 2 / a)
    (B := 2 * Real.sqrt 2)
    (G := n * (inverseJetConstant n + a⁻¹ * (2 * n ^ 2 * inverseJetConstant n ^ 2)))
    (A := 2 * tensorSecondBernsteinConstant n) (c := c)
    (by positivity) (by positivity) (by positivity) (by positivity) hc
    (fun y => ⟨div_nonneg (tensorDerivativeSquare_nonneg v y) ha.le,
      div_le_div_of_nonneg_right (tensorDerivativeSquare_uniform hv hi hAC y) ha.le⟩)
    (fun y => ⟨(div_nonneg (diffuseDefect_nonneg (smooth_C2 hv) hi hAC y) (by norm_num)).trans
      (defectCarrier_bounds hv hi hAC y).1,
      (defectCarrier_bounds hv hi hAC y).2.trans (diffuseDefect_le_one v y)⟩)
    (diffuseDrift_bound (smooth_C2 hv) hi hAC) (defectCarrier_gradient_bound hv hi hAC)
    hfde (defectCarrier_drift_upper hv hi hAC) x
  have HH' := HH.trans (mul_le_mul_of_nonneg_left (defectCarrier_bounds hv hi hAC x).2 (by positivity))
  change tensorDerivativeSquare v x / a ≤ _ at HH'
  have Hfinal := (div_le_iff₀ ha).mp HH'
  dsimp only [derivativeDefectConstant]
  dsimp only [a,c] at Hfinal
  nlinarith

lemma coordDeriv_square {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) (x : Space n) : coordDeriv (fun y => f y ^ 2) i x = 2 * f x * coordDeriv f i x := by
  simp only [pow_two]
  rw [coordDeriv_mul hf hf]; ring

lemma coordDeriv_hessianSquare {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (k : Fin n) (x : Space n) :
    coordDeriv (hessianSquare v) k x = ∑ i : Fin n, ∑ j : Fin n,
      2 * inverseHessian v i j x * coordDeriv (inverseHessian v i j) k x := by
  have hT (i j : Fin n) := (inverseHessian_smooth hv hi i j).differentiable (by simp)
  have he : hessianSquare v = fun y => ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j y ^ 2 :=
    funext (hessianSquare_eq_sum v)
  rw [he, coordDeriv_sum _ (fun i _ => Differentiable.fun_sum (fun j _ => (hT i j).fun_pow 2))]
  apply Finset.sum_congr rfl; intro i _
  rw [coordDeriv_sum _ (fun j _ => (hT i j).fun_pow 2)]
  apply Finset.sum_congr rfl; intro j _
  exact coordDeriv_square (hT i j) k x

lemma coordDeriv_hessianSquare_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (k : Fin n) (x : Space n) : |coordDeriv (hessianSquare v) k x| ≤
      (tensorBernsteinConstant n + 3 + derivativeDefectConstant n) * diffuseDefect v x := by
  rw [coordDeriv_hessianSquare hv hi]
  have hh (i j : Fin n) : |2 * inverseHessian v i j x * coordDeriv (inverseHessian v i j) k x| ≤
      inverseHessian v i j x ^ 2 + ‖gradient (inverseHessian v i j) x‖ ^ 2 := by
    have hc := coordDeriv_abs_le_gradient (inverseHessian v i j) k x
    have hc2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
    have hy := sq_nonneg (|inverseHessian v i j x| - |coordDeriv (inverseHessian v i j) k x|)
    simp only [sq_abs] at hc2 hy
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_abs (inverseHessian v i j x), sq_abs (coordDeriv (inverseHessian v i j) k x)]
  calc |∑ i : Fin n, ∑ j : Fin n, 2 * inverseHessian v i j x * coordDeriv (inverseHessian v i j) k x| ≤
      ∑ i : Fin n, ∑ j : Fin n, |2 * inverseHessian v i j x * coordDeriv (inverseHessian v i j) k x| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (inverseHessian v i j x ^ 2 + ‖gradient (inverseHessian v i j) x‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hh i j))
    _ = hessianSquare v x + tensorDerivativeSquare v x := by
      simp only [Finset.sum_add_distrib, ← hessianSquare_eq_sum, tensorDerivativeSquare]
    _ ≤ _ := by linarith [hessianSquare_le_defect hv hi hAC x, tensorDerivativeSquare_le_defect hv hi hAC x]

def defectPotential {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  2 * (defectWeight v x * (1 - diffuseDefect v x))

def defectSource {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  defectPotential v x * diffuseDefect v x - 2 * hessianSquare v x

def defectPotentialConstant (n : ℕ) : ℝ := 8 * inverseJetConstant n * (1 + inverseJetConstant n)

def defectSourceConstant (n : ℕ) : ℝ := defectPotentialConstant n +
  2 * ((tensorBernsteinConstant n + 3 + derivativeDefectConstant n) + (tensorBernsteinConstant n + 3)) + 1

lemma defectPotentialConstant_nonneg (n : ℕ) : 0 ≤ defectPotentialConstant n := by
  have hJ := inverseJetConstant_one_le n
  dsimp [defectPotentialConstant]; positivity

lemma defectSourceConstant_pos (n : ℕ) : 0 < defectSourceConstant n := by
  have hP := defectPotentialConstant_nonneg n
  have hE := derivativeDefectConstant_pos n
  have hB : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  dsimp [defectSourceConstant]; positivity

lemma defectPotential_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (defectPotential v) :=
  contDiff_const.mul ((contDiff_const.sub (hv.pow 2)).mul (contDiff_const.sub (diffuseDefect_smooth hv hi)))

lemma defectSource_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (defectSource v) :=
  ((defectPotential_smooth hv hi).mul (diffuseDefect_smooth hv hi)).sub
    (contDiff_const.mul (hessianSquare_smooth hv hi))

lemma defectPotential_C1Bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v) :
    C1Bound (defectPotential v) (defectPotentialConstant n) := by
  have hJ : 0 ≤ inverseJetConstant n := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseJetConstant_one_le n)
  have hq := (inverseJet_C1Bound hv hi hAC).2.1
  have hD := (inverseJet_C1Bound hv hi hAC).2.2.1
  have hdq : Differentiable ℝ (defectWeight v) := (contDiff_const.sub (hv.pow 2)).differentiable (by simp)
  have hdD := (diffuseDefect_smooth hv hi).differentiable (by simp)
  have hh := (C1Bound.const (n := n) 1).sub (differentiable_const 1) hdD hD
  simp only [abs_one] at hh
  have hprod := hq.mul hdq ((differentiable_const 1).sub hdD) (by positivity) (by positivity) hh
  have hm := hprod.const_mul (hdq.mul ((differentiable_const 1).sub hdD)) (by positivity) 2
  convert hm using 1
  · rfl
  · dsimp [defectPotentialConstant]; norm_num; ring

lemma diffuseDefect_drift_eq_source {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v) (x : Space n) :
    Laplacian.laplacian (diffuseDefect v) x - fderiv ℝ (diffuseDefect v) x (diffuseDrift v x) =
      defectSource v x := by
  rw [diffuseDefect_laplacian hv hi hAC]
  rw [diffuseDrift, map_smul, smul_eq_mul, ← inner_gradient_left, real_inner_comm]
  dsimp only [defectSource, defectPotential, diffuseDefect, hessianSquare]
  ring

lemma defectSource_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v) :
    (∀ x, |defectSource v x| ≤ defectSourceConstant n * diffuseDefect v x) ∧
    ∀ i x, |coordDeriv (defectSource v) i x| ≤ defectSourceConstant n *
      (diffuseDefect v x + |coordDeriv (diffuseDefect v) i x|) := by
  have hB : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  have hE := derivativeDefectConstant_pos n
  have hP := defectPotentialConstant_nonneg n
  have hc := defectPotential_C1Bound hv hi hAC
  have hdP := (defectPotential_smooth hv hi).differentiable (by simp)
  have hdD := (diffuseDefect_smooth hv hi).differentiable (by simp)
  have hdF := (hessianSquare_smooth hv hi).differentiable (by simp)
  constructor
  · intro x
    have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
    have hF := hessianSquare_nonneg v x
    calc |defectSource v x| ≤ |defectPotential v x * diffuseDefect v x| + |2 * hessianSquare v x| := abs_sub _ _
      _ ≤ defectPotentialConstant n * diffuseDefect v x + 2 * hessianSquare v x := by
        simp only [abs_mul, abs_of_nonneg hD, abs_of_nonneg hF, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add (mul_le_mul_of_nonneg_right (hc.1 x) hD) le_rfl
      _ ≤ _ := by
        have hh := hessianSquare_le_defect hv hi hAC x
        have hp : 0 ≤ 2 * (tensorBernsteinConstant n + 3 + derivativeDefectConstant n) * diffuseDefect v x := by positivity
        dsimp [defectSourceConstant]; nlinarith
  · intro i x
    have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
    have he : coordDeriv (defectSource v) i x =
        coordDeriv (fun y => defectPotential v y * diffuseDefect v y) i x -
          2 * coordDeriv (hessianSquare v) i x := by
      change fderiv ℝ (fun y => defectPotential v y * diffuseDefect v y - 2 * hessianSquare v y) x (basis n i) = _
      rw [fderiv_fun_sub ((hdP.fun_mul hdD) x) ((hdF.const_mul 2) x), sub_apply,
        fderiv_const_mul (hdF x)]
      rfl
    rw [he]
    apply ((abs_sub _ _).trans (add_le_add
      (coordDeriv_mul_estimate hdP hdD hP hc i x) (show |2 * coordDeriv (hessianSquare v) i x| ≤
        2 * ((tensorBernsteinConstant n + 3 + derivativeDefectConstant n) * diffuseDefect v x) by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_mul_of_nonneg_left (coordDeriv_hessianSquare_bound hv hi hAC i x) (by norm_num)))).trans
    rw [abs_of_nonneg hD]
    have ht := abs_nonneg (coordDeriv (diffuseDefect v) i x)
    have hdiff : 0 ≤ (2 * (tensorBernsteinConstant n + 3) + 1) * diffuseDefect v x +
        (2 * ((tensorBernsteinConstant n + 3 + derivativeDefectConstant n) + (tensorBernsteinConstant n + 3)) + 1) *
          |coordDeriv (diffuseDefect v) i x| := by positivity
    dsimp [defectSourceConstant]; nlinarith

lemma drift_log_bochner {n : ℕ} {v h r : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hh : ContDiff ℝ ∞ h) (hr : ContDiff ℝ ∞ r)
    (heq : ∀ x, Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2)
    (x : Space n) :
    Laplacian.laplacian (fun y => ‖gradient h y‖ ^ 2) x -
      fderiv ℝ (fun y => ‖gradient h y‖ ^ 2) x (diffuseDrift v x - (2 : ℝ) • gradient h x) =
    2 * (∑ i : Fin n, ‖gradient (coordDeriv h i) x‖ ^ 2) +
      2 * (∑ i : Fin n, coordDeriv h i x * coordDeriv r i x) +
      2 * (∑ i : Fin n, coordDeriv h i x * ∑ k : Fin n, coordDeriv (driftCoeff v k) i x * coordDeriv h k x) := by
  let w := fun y => ‖gradient h y‖ ^ 2
  have hw : ContDiff ℝ ∞ w := gradient_norm_sq_smooth hh
  have hd (i : Fin n) := smooth_C2 (coordDeriv_smooth hh i)
  have hL (i : Fin n) :
      Laplacian.laplacian (coordDeriv h i) x - fderiv ℝ (coordDeriv h i) x (diffuseDrift v x) =
      coordDeriv r i x - coordDeriv w i x +
        ∑ k : Fin n, coordDeriv (driftCoeff v k) i x * coordDeriv h k x := by
    rw [diffuse_drift_commute hv hi hh (hr.sub hw) heq]
    rw [coordDeriv_sub (hr.differentiable (by simp)) (hw.differentiable (by simp))]
  have he : w = fun y => ∑ i : Fin n, coordDeriv h i y ^ 2 := funext (gradient_norm_sq h)
  have hWL : Laplacian.laplacian w x - fderiv ℝ w x (diffuseDrift v x) =
      2 * (∑ i : Fin n, ‖gradient (coordDeriv h i) x‖ ^ 2) +
        2 * (∑ i : Fin n, coordDeriv h i x * coordDeriv r i x) -
        2 * (∑ i : Fin n, coordDeriv h i x * coordDeriv w i x) +
        2 * (∑ i : Fin n, coordDeriv h i x * ∑ k : Fin n, coordDeriv (driftCoeff v k) i x * coordDeriv h k x) := by
    conv_lhs => rw [he, drift_sum_identity _ (fun i _ => (hd i).pow 2)]
    simp_rw [drift_square_identity (hd _) (diffuseDrift v) x, hL]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hg : fderiv ℝ w x (gradient h x) = ∑ i : Fin n, coordDeriv h i x * coordDeriv w i x := by
    rw [← inner_gradient_left, real_inner_comm, inner_gradient_eq_sum]
  change Laplacian.laplacian w x - fderiv ℝ w x (diffuseDrift v x - (2 : ℝ) • gradient h x) = _
  rw [map_sub, map_smul, smul_eq_mul, hg]
  linarith [hWL]

lemma laplacian_sq_le_hessian {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space n) :
    Laplacian.laplacian f x ^ 2 ≤ n * ∑ i : Fin n, ‖gradient (coordDeriv f i) x‖ ^ 2 := by
  rw [laplacian_eq_sum_coordDeriv (smooth_C2 hf)]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun i : Fin n => coordDeriv (coordDeriv f i) i x) (fun _ : Fin n => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  apply hc.trans
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  have hh := pow_le_pow_left₀ (abs_nonneg _) (coordDeriv_abs_le_gradient (coordDeriv f i) i x) 2
  simpa only [sq_abs] using hh

lemma log_bochner_lower {n : ℕ} {v h r : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (hh : ContDiff ℝ ∞ h) (hr : ContDiff ℝ ∞ r) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (heq : ∀ x, Laplacian.laplacian h x - fderiv ℝ h x (diffuseDrift v x) = r x - ‖gradient h x‖ ^ 2)
    (hrb : ∀ i x, |coordDeriv r i x| ≤ R * (1 + |coordDeriv h i x|))
    (hcb : ∀ i k x, |coordDeriv (driftCoeff v k) i x| ≤ C) (x : Space n) :
    2 * (∑ i : Fin n, ‖gradient (coordDeriv h i) x‖ ^ 2) -
      R * n - (3 * R + 2 * C * n) * ‖gradient h x‖ ^ 2 ≤
    Laplacian.laplacian (fun y => ‖gradient h y‖ ^ 2) x -
      fderiv ℝ (fun y => ‖gradient h y‖ ^ 2) x (diffuseDrift v x - (2 : ℝ) • gradient h x) := by
  have hp (i : Fin n) : -(R * (1 + 3 * coordDeriv h i x ^ 2)) ≤
      2 * coordDeriv h i x * coordDeriv r i x := by
    have hm := mul_le_mul_of_nonneg_left (hrb i x) (show 0 ≤ 2 * |coordDeriv h i x| by positivity)
    have hlow : -(2 * |coordDeriv h i x| * |coordDeriv r i x|) ≤ 2 * coordDeriv h i x * coordDeriv r i x := by
      have ht := neg_abs_le (2 * coordDeriv h i x * coordDeriv r i x)
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hs := mul_nonneg hR (sq_nonneg (|coordDeriv h i x| - 1))
    nlinarith [sq_abs (coordDeriv h i x)]
  have hd (i k : Fin n) : -(C * (coordDeriv h i x ^ 2 + coordDeriv h k x ^ 2)) ≤
      2 * coordDeriv h i x * (coordDeriv (driftCoeff v k) i x * coordDeriv h k x) := by
    have hm := mul_le_mul_of_nonneg_left (hcb i k x)
      (show 0 ≤ 2 * |coordDeriv h i x| * |coordDeriv h k x| by positivity)
    have hlow := neg_abs_le (2 * coordDeriv h i x * (coordDeriv (driftCoeff v k) i x * coordDeriv h k x))
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hlow
    have hs := mul_nonneg hC (sq_nonneg (|coordDeriv h i x| - |coordDeriv h k x|))
    nlinarith [sq_abs (coordDeriv h i x), sq_abs (coordDeriv h k x)]
  have HP := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => hp i)
  have HD := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (k : Fin n) (_ : k ∈ Finset.univ) => hd i k))
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← mul_assoc,
    ← gradient_norm_sq] at HP HD
  simp only [mul_assoc, ← Finset.mul_sum] at HP HD
  rw [drift_log_bochner hv hi hh hr heq]
  nlinarith

lemma bounded_drift_logistic_scaled {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M B A N : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hA : 0 ≤ A) (hN : 0 < N)
    (hfb : ∀ x, |f x| ≤ M) (hbb : ∀ x, ‖b x‖ ≤ B)
    (hpde : ∀ x, f x ^ 2 - A * N * f x - A * N ^ 2 ≤
      N * (Laplacian.laplacian f x - fderiv ℝ f x (b x))) :
    ∀ x, f x ≤ N * (A + 1) := by
  let g := fun x => f x / N
  have hg : ContDiff ℝ 2 g := hf.div_const N
  have hgb (x : Space n) : |g x| ≤ M / N := by
    dsimp [g]; rw [abs_div, abs_of_pos hN]; exact div_le_div_of_nonneg_right (hfb x) hN.le
  have hLg (x : Space n) : Laplacian.laplacian g x - fderiv ℝ g x (b x) =
      (Laplacian.laplacian f x - fderiv ℝ f x (b x)) / N := by
    have he : g = fun y => N⁻¹ * f y := by funext y; dsimp [g]; rw [div_eq_mul_inv, mul_comm]
    rw [he, drift_const_mul hf]
    simp only [div_eq_mul_inv, mul_comm]
  have hl (x : Space n) : g x ^ 2 - A * g x - A ≤
      Laplacian.laplacian g x - fderiv ℝ g x (b x) := by
    rw [hLg]
    apply (le_div_iff₀ hN).mpr
    apply (mul_le_mul_iff_right₀ hN).mp
    have he : N * ((g x ^ 2 - A * g x - A) * N) = f x ^ 2 - A * N * f x - A * N ^ 2 := by
      dsimp [g]; field_simp
    rw [he]
    exact hpde x
  have HH := bounded_drift_logistic hg b (div_nonneg hM hN.le) hB hA hgb hbb hl
  intro x
  have hh := (div_le_iff₀ hN).mp (HH x)
  simpa only [mul_comm] using hh

end DeGiorgi
end

end OAI
