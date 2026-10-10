import OAI.Analysis.AllenCahn.TensorBounds

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma inverseJet_C1Bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v) :
    C1Bound v (inverseJetConstant n) ∧ C1Bound (defectWeight v) (2 * inverseJetConstant n) ∧
    C1Bound (diffuseDefect v) (inverseJetConstant n) ∧
    (∀ i, C1Bound (coordDeriv (inverseProfile v) i) (inverseJetConstant n)) ∧
    (∀ i j, C1Bound (inverseHessian v i j) (inverseJetConstant n)) := by
  let K := 12 * (2 * Real.sqrt 2 + 1)
  let J := inverseJetConstant n
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ1 : 1 ≤ J := inverseJetConstant_one_le n
  have hJK : K ≤ J := by
    dsimp [J, inverseJetConstant]
    have hc : 0 ≤ tensorSystemConstant n := by dsimp [tensorSystemConstant]; positivity
    have hh : 0 ≤ 2 * (2 * K + tensorSystemConstant n * (1 + (n + 1) * K) + 3) * (2 * Real.sqrt 2 + 1) := by positivity
    change K ≤ 1 + K + 2 * n * K + _
    nlinarith [show 0 ≤ (n : ℝ) by positivity]
  have hJG : 2 * (n : ℝ) * K ≤ J := by
    dsimp [J, inverseJetConstant]
    have hc : 0 ≤ tensorSystemConstant n := by dsimp [tensorSystemConstant]; positivity
    have hh : 0 ≤ 2 * (2 * K + tensorSystemConstant n * (1 + (n + 1) * K) + 3) * (2 * Real.sqrt 2 + 1) := by positivity
    change 2 * n * K ≤ 1 + K + 2 * n * K + _
    linarith
  have hJT : 2 * (2 * K + tensorSystemConstant n * (1 + (n + 1) * K) + 3) * (2 * Real.sqrt 2 + 1) ≤ J := by
    dsimp [J, inverseJetConstant]
    change _ ≤ 1 + K + 2 * n * K + _
    have hh : 0 ≤ 2 * (n : ℝ) * K := by positivity
    linarith
  have hp (i : Fin n) (x : Space n) : |coordDeriv (inverseProfile v) i x| ≤ 1 :=
    (coordDeriv_abs_le_gradient _ _ _).trans (inverseProfile_gradient_bound (smooth_C2 hv) hi hAC x)
  have hvb (x : Space n) : |v x| ≤ 1 := (abs_lt.mpr (hi x)).le
  have hq (x : Space n) : |defectWeight v x| ≤ 1 := by
    have hqpos : 0 < defectWeight v x := weight_pos (hi x)
    rw [abs_of_pos hqpos]
    dsimp [defectWeight]; nlinarith [sq_nonneg (v x)]
  have hvd (i : Fin n) (x : Space n) : |coordDeriv v i x| ≤ 1 := by
    rw [coordDeriv_profile (hv.differentiable (by simp)) hi, abs_mul, abs_div]
    have hsd : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [abs_of_pos hsd]
    exact (mul_le_mul (div_le_one_of_le₀ ((hq x).trans hs1) hsd.le) (hp i x)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  refine ⟨⟨fun x => (hvb x).trans hJ1, fun i x => (hvd i x).trans hJ1⟩, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro x; exact (hq x).trans (by linarith)
    · intro i x
      have he : coordDeriv (defectWeight v) i x = -2 * v x * coordDeriv v i x := by
        change fderiv ℝ (fun y => 1 - v y ^ 2) x (basis n i) = _
        rw [fderiv_fun_sub (g := fun y => v y ^ 2) (differentiableAt_const 1)
          ((hv.differentiable (by simp) x).pow 2)]
        simp [fderiv_fun_pow 2 (hv.differentiable (by simp) x), coordDeriv, mul_assoc]
      rw [he, abs_mul, abs_mul]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hh := mul_le_mul (hvb x) (hvd i x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
  · constructor
    · intro x
      rw [abs_of_nonneg (diffuseDefect_nonneg (smooth_C2 hv) hi hAC x)]
      exact (diffuseDefect_le_one v x).trans hJ1
    · intro i x; exact (coordDeriv_diffuseDefect_uniform_bound hv hi hAC i x).trans hJG
  · intro i
    refine ⟨fun x => (hp i x).trans hJ1, ?_⟩
    intro j x
    exact (inverseHessian_abs_le hv hi hAC i j x).trans hJK
  · intro i j
    refine ⟨fun x => (inverseHessian_abs_le hv hi hAC i j x).trans hJK, ?_⟩
    intro k x
    exact (coordDeriv_abs_le_gradient _ _ _).trans
      ((inverseHessian_gradient_uniform_bound hv hi hAC i j x).trans hJT)

def tensorCoeffZero {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  -(defectWeight v x * diffuseDefect v x)

def tensorCoeffSource {n : ℕ} (v : Space n → ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  Real.sqrt 2 * (v x * defectWeight v x * coordDeriv (inverseProfile v) i x *
    coordDeriv (inverseProfile v) j x)

def tensorCoeffFirst {n : ℕ} (v : Space n → ℝ) (i k : Fin n) (x : Space n) : ℝ :=
  2 * (defectWeight v x * coordDeriv (inverseProfile v) i x * coordDeriv (inverseProfile v) k x)

def tensorCoeffSecond {n : ℕ} (v : Space n → ℝ) (i k : Fin n) (x : Space n) : ℝ :=
  (2 * Real.sqrt 2) * (v x * inverseHessian v i k x)

def driftCoeff {n : ℕ} (v : Space n → ℝ) (k : Fin n) (x : Space n) : ℝ :=
  (2 * Real.sqrt 2) * (v x * coordDeriv (inverseProfile v) k x)

def tensorCoeffConstant (n : ℕ) : ℝ :=
  let J := inverseJetConstant n
  1 + 2 * (2 * J) * J + Real.sqrt 2 * (2 * (2 * (2 * J * (2 * J)) * J) * J) +
    2 * (2 * (2 * (2 * J) * J) * J) + (2 * Real.sqrt 2) * (2 * J * J)

lemma tensorCoeffConstant_pos (n : ℕ) : 0 < tensorCoeffConstant n := by
  have hJ : 0 ≤ inverseJetConstant n := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseJetConstant_one_le n)
  dsimp [tensorCoeffConstant]; positivity

lemma tensorCoeff_C1Bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v) :
    C1Bound (tensorCoeffZero v) (tensorCoeffConstant n) ∧
    (∀ i j, C1Bound (tensorCoeffSource v i j) (tensorCoeffConstant n)) ∧
    (∀ i k, C1Bound (tensorCoeffFirst v i k) (tensorCoeffConstant n)) ∧
    (∀ i k, C1Bound (tensorCoeffSecond v i k) (tensorCoeffConstant n)) ∧
    (∀ k, C1Bound (driftCoeff v k) (tensorCoeffConstant n)) := by
  obtain ⟨hvb,hqb,hDb,hpb,hTb⟩ := inverseJet_C1Bound hv hi hAC
  let J := inverseJetConstant n
  have hJ : 0 ≤ J := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseJetConstant_one_le n)
  have hu := inverseProfile_smooth hv hi
  have hdv := hv.differentiable (by simp)
  have hdq : Differentiable ℝ (defectWeight v) :=
    differentiable_const 1 |>.sub (hdv.pow 2)
  have hdD := (diffuseDefect_smooth hv hi).differentiable (by simp)
  have hdp (k : Fin n) := (coordDeriv_smooth hu k).differentiable (by simp)
  have hdT (i k : Fin n) := (inverseHessian_smooth hv hi i k).differentiable (by simp)
  have hC0 : 2 * (2 * J) * J ≤ tensorCoeffConstant n := by
    dsimp [tensorCoeffConstant]; change _ ≤ 1 + 2 * (2 * J) * J + _ + _ + _
    have h₁ : 0 ≤ Real.sqrt 2 * (2 * (2 * (2 * J * (2 * J)) * J) * J) := by positivity
    have h₂ : 0 ≤ 2 * (2 * (2 * (2 * J) * J) * J) := by positivity
    have h₃ : 0 ≤ (2 * Real.sqrt 2) * (2 * J * J) := by positivity
    linarith
  have hC1 : Real.sqrt 2 * (2 * (2 * (2 * J * (2 * J)) * J) * J) ≤ tensorCoeffConstant n := by
    dsimp [tensorCoeffConstant]; change _ ≤ 1 + 2 * (2 * J) * J + _ + _ + _
    have h₀ : 0 ≤ 2 * (2 * J) * J := by positivity
    have h₂ : 0 ≤ 2 * (2 * (2 * (2 * J) * J) * J) := by positivity
    have h₃ : 0 ≤ (2 * Real.sqrt 2) * (2 * J * J) := by positivity
    linarith
  have hC2 : 2 * (2 * (2 * (2 * J) * J) * J) ≤ tensorCoeffConstant n := by
    dsimp [tensorCoeffConstant]; change _ ≤ 1 + 2 * (2 * J) * J + _ + _ + _
    have h₀ : 0 ≤ 2 * (2 * J) * J := by positivity
    have h₁ : 0 ≤ Real.sqrt 2 * (2 * (2 * (2 * J * (2 * J)) * J) * J) := by positivity
    have h₃ : 0 ≤ (2 * Real.sqrt 2) * (2 * J * J) := by positivity
    linarith
  have hC4 : (2 * Real.sqrt 2) * (2 * J * J) ≤ tensorCoeffConstant n := by
    dsimp [tensorCoeffConstant]; change _ ≤ 1 + 2 * (2 * J) * J + _ + _ + _
    have h₀ : 0 ≤ 2 * (2 * J) * J := by positivity
    have h₁ : 0 ≤ Real.sqrt 2 * (2 * (2 * (2 * J * (2 * J)) * J) * J) := by positivity
    have h₂ : 0 ≤ 2 * (2 * (2 * (2 * J) * J) * J) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((hqb.mul hdq hdD (by positivity) hJ hDb).neg (hdq.mul hdD)).mono hC0
  · intro i j
    have H := (((hvb.mul hdv hdq hJ (by positivity) hqb).mul (hdv.mul hdq) (hdp i)
      (by positivity) hJ (hpb i)).mul ((hdv.mul hdq).mul (hdp i)) (hdp j)
      (by positivity) hJ (hpb j)).const_mul (((hdv.mul hdq).mul (hdp i)).mul (hdp j))
      (by positivity) (Real.sqrt 2)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at H
    exact H.mono hC1
  · intro i k
    have H := ((hqb.mul hdq (hdp i) (by positivity) hJ (hpb i)).mul
      (hdq.mul (hdp i)) (hdp k) (by positivity) hJ (hpb k)).const_mul
      ((hdq.mul (hdp i)).mul (hdp k)) (by positivity) 2
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H
    exact H.mono hC2
  · intro i k
    have H := (hvb.mul hdv (hdT i k) hJ hJ (hTb i k)).const_mul
      (hdv.mul (hdT i k)) (by positivity) (2 * Real.sqrt 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 2)] at H
    exact H.mono hC4
  · intro k
    have H := (hvb.mul hdv (hdp k) hJ hJ (hpb k)).const_mul
      (hdv.mul (hdp k)) (by positivity) (2 * Real.sqrt 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 2)] at H
    exact H.mono hC4

lemma tensorCoeff_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (tensorCoeffZero v) ∧
    (∀ i j, ContDiff ℝ ∞ (tensorCoeffSource v i j)) ∧
    (∀ i k, ContDiff ℝ ∞ (tensorCoeffFirst v i k)) ∧
    (∀ i k, ContDiff ℝ ∞ (tensorCoeffSecond v i k)) ∧
    (∀ k, ContDiff ℝ ∞ (driftCoeff v k)) := by
  have hq : ContDiff ℝ ∞ (defectWeight v) := contDiff_const.sub (hv.pow 2)
  have hp (k : Fin n) := coordDeriv_smooth (inverseProfile_smooth hv hi) k
  have hT (i k : Fin n) := inverseHessian_smooth hv hi i k
  refine ⟨(hq.mul (diffuseDefect_smooth hv hi)).neg, ?_, ?_, ?_, ?_⟩
  · intro i j; exact contDiff_const.mul (((hv.mul hq).mul (hp i)).mul (hp j))
  · intro i k; exact contDiff_const.mul ((hq.mul (hp i)).mul (hp k))
  · intro i k; exact contDiff_const.mul (hv.mul (hT i k))
  · intro k; exact contDiff_const.mul (hv.mul (hp k))

def tensorSource {n : ℕ} (v : Space n → ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  tensorCoeffZero v x * inverseHessian v i j x + tensorCoeffSource v i j x * diffuseDefect v x +
    (∑ k : Fin n, tensorCoeffFirst v i k x * inverseHessian v j k x) +
    (∑ k : Fin n, tensorCoeffFirst v j k x * inverseHessian v i k x) +
    (∑ k : Fin n, tensorCoeffSecond v i k x * inverseHessian v k j x)

lemma inverseHessian_drift_factored {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j : Fin n) (x : Space n) :
    Laplacian.laplacian (inverseHessian v i j) x -
      fderiv ℝ (inverseHessian v i j) x (diffuseDrift v x) = tensorSource v i j x := by
  rw [inverseHessian_drift_system hv hi hAC, coordDeriv_diffuseDefect_sum hv hi,
    coordDeriv_diffuseDefect_sum hv hi]
  have hs (a b : Fin n) : (∑ k : Fin n, tensorCoeffFirst v a k x * inverseHessian v b k x) =
      2 * defectWeight v x * coordDeriv (inverseProfile v) a x *
        ∑ k : Fin n, coordDeriv (inverseProfile v) k x * inverseHessian v b k x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; dsimp [tensorCoeffFirst]; ring
  have ht : (∑ k : Fin n, tensorCoeffSecond v i k x * inverseHessian v k j x) =
      2 * Real.sqrt 2 * v x * ∑ k : Fin n, inverseHessian v i k x * inverseHessian v k j x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; dsimp [tensorCoeffSecond]; ring
  dsimp only [tensorSource]
  rw [hs, hs, ht]
  dsimp [tensorCoeffZero, tensorCoeffSource]
  ring

lemma tensorSource_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (i j : Fin n) :
    ContDiff ℝ ∞ (tensorSource v i j) := by
  obtain ⟨h0,h1,h2,h3,_⟩ := tensorCoeff_smooth hv hi
  have hT (a b : Fin n) := inverseHessian_smooth hv hi a b
  exact ((((h0.mul (hT i j)).add ((h1 i j).mul (diffuseDefect_smooth hv hi))).add
    (ContDiff.sum (fun k _ => (h2 i k).mul (hT j k)))).add
    (ContDiff.sum (fun k _ => (h2 j k).mul (hT i k)))).add
    (ContDiff.sum (fun k _ => (h3 i k).mul (hT k j)))

def tensorDerivativeSquare {n : ℕ} (v : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖gradient (inverseHessian v i j) x‖ ^ 2

lemma tensorDerivativeSquare_nonneg {n : ℕ} (v : Space n → ℝ) (x : Space n) :
    0 ≤ tensorDerivativeSquare v x := by
  dsimp [tensorDerivativeSquare]; positivity

lemma tensorDerivativeSquare_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiff ℝ ∞ (tensorDerivativeSquare v) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    gradient_norm_sq_smooth (inverseHessian_smooth hv hi i j)))

lemma inverseHessian_deriv_abs_le_sqrt {n : ℕ} (v : Space n → ℝ) (i j k : Fin n) (x : Space n) :
    |coordDeriv (inverseHessian v i j) k x| ≤ Real.sqrt (tensorDerivativeSquare v x) := by
  have hg : ‖gradient (inverseHessian v i j) x‖ ^ 2 ≤ tensorDerivativeSquare v x := by
    apply le_trans (Finset.single_le_sum (fun (j : Fin n) (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖gradient (inverseHessian v i j) x‖) (Finset.mem_univ j))
    exact Finset.single_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) =>
      Finset.sum_nonneg (fun j _ => sq_nonneg ‖gradient (inverseHessian v i j) x‖)) (Finset.mem_univ i)
  apply (coordDeriv_abs_le_gradient _ _ _).trans
  nlinarith [Real.sq_sqrt (tensorDerivativeSquare_nonneg v x),
    Real.sqrt_nonneg (tensorDerivativeSquare v x), norm_nonneg (gradient (inverseHessian v i j) x)]

lemma coordDeriv_mul_estimate {n : ℕ} {f g : Space n → ℝ} {C : ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (hC : 0 ≤ C) (h : C1Bound f C)
    (k : Fin n) (x : Space n) :
    |coordDeriv (fun y => f y * g y) k x| ≤ C * (|g x| + |coordDeriv g k x|) := by
  rw [coordDeriv_mul hf hg]
  calc |f x * coordDeriv g k x + g x * coordDeriv f k x| ≤
      |f x * coordDeriv g k x| + |g x * coordDeriv f k x| := abs_add_le _ _
    _ ≤ C * |coordDeriv g k x| + |g x| * C := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (h.1 x) le_rfl (abs_nonneg _) hC)
        (mul_le_mul_of_nonneg_left (h.2 k x) (abs_nonneg _))
    _ = _ := by ring

lemma coordDeriv_add {n : ℕ} {f g : Space n → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin n) (x : Space n) :
    coordDeriv (fun y => f y + g y) i x = coordDeriv f i x + coordDeriv g i x := by
  simp only [coordDeriv, fderiv_fun_add (hf x) (hg x), add_apply]

lemma tensorSource_coord_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j k : Fin n) (x : Space n) :
    |coordDeriv (tensorSource v i j) k x| ≤ tensorCoeffConstant n * (1 + 5 * n) *
      (diffuseDefect v x + Real.sqrt (hessianSquare v x) + Real.sqrt (tensorDerivativeSquare v x)) := by
  obtain ⟨hb0,hb1,hb2,hb3,_⟩ := tensorCoeff_C1Bound hv hi hAC
  obtain ⟨hc0,hc1,hc2,hc3,_⟩ := tensorCoeff_smooth hv hi
  have hd0 := hc0.differentiable (by simp)
  have hd1 (a b : Fin n) := (hc1 a b).differentiable (by simp)
  have hd2 (a b : Fin n) := (hc2 a b).differentiable (by simp)
  have hd3 (a b : Fin n) := (hc3 a b).differentiable (by simp)
  have hdT (a b : Fin n) := (inverseHessian_smooth hv hi a b).differentiable (by simp)
  have hdD := (diffuseDefect_smooth hv hi).differentiable (by simp)
  let C := tensorCoeffConstant n
  let S := Real.sqrt (hessianSquare v x)
  let Q := Real.sqrt (tensorDerivativeSquare v x)
  have hC : 0 ≤ C := (tensorCoeffConstant_pos n).le
  have hD : 0 ≤ diffuseDefect v x := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hprod {f : Space n → ℝ} (hf : Differentiable ℝ f) (hb : C1Bound f C) (a b : Fin n) :
      |coordDeriv (fun y => f y * inverseHessian v a b y) k x| ≤ C * (S + Q) :=
    (coordDeriv_mul_estimate hf (hdT a b) hC hb k x).trans
      (mul_le_mul_of_nonneg_left (add_le_add (inverseHessian_abs_le_sqrt v a b x)
        (inverseHessian_deriv_abs_le_sqrt v a b k x)) hC)
  have hprodD : |coordDeriv (fun y => tensorCoeffSource v i j y * diffuseDefect v y) k x| ≤
      C * (diffuseDefect v x + 2 * n * S) := by
    apply (coordDeriv_mul_estimate (hd1 i j) hdD hC (hb1 i j) k x).trans
    rw [abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left (add_le_add_right (coordDeriv_diffuseDefect_bound hv hi hAC k x) _) hC
  have hsum {f : Fin n → Space n → ℝ} (hf : ∀ l, Differentiable ℝ (f l))
      (hb : ∀ l, |coordDeriv (f l) k x| ≤ C * (S + Q)) :
      |coordDeriv (fun y => ∑ l : Fin n, f l y) k x| ≤ n * (C * (S + Q)) := by
    rw [coordDeriv_sum _ (fun l _ => hf l)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun l _ => hb l)).trans_eq (by simp))
  have hs1 := hsum (fun l => (hd2 i l).mul (hdT j l)) (fun l => hprod (hd2 i l) (hb2 i l) j l)
  have hs2 := hsum (fun l => (hd2 j l).mul (hdT i l)) (fun l => hprod (hd2 j l) (hb2 j l) i l)
  have hs3 := hsum (fun l => (hd3 i l).mul (hdT l j)) (fun l => hprod (hd3 i l) (hb3 i l) l j)
  have he : coordDeriv (tensorSource v i j) k x =
      coordDeriv (fun y => tensorCoeffZero v y * inverseHessian v i j y) k x +
      coordDeriv (fun y => tensorCoeffSource v i j y * diffuseDefect v y) k x +
      coordDeriv (fun y => ∑ l : Fin n, tensorCoeffFirst v i l y * inverseHessian v j l y) k x +
      coordDeriv (fun y => ∑ l : Fin n, tensorCoeffFirst v j l y * inverseHessian v i l y) k x +
      coordDeriv (fun y => ∑ l : Fin n, tensorCoeffSecond v i l y * inverseHessian v l j y) k x := by
    change coordDeriv (fun y =>
      tensorCoeffZero v y * inverseHessian v i j y + tensorCoeffSource v i j y * diffuseDefect v y +
        (∑ l : Fin n, tensorCoeffFirst v i l y * inverseHessian v j l y) +
        (∑ l : Fin n, tensorCoeffFirst v j l y * inverseHessian v i l y) +
        (∑ l : Fin n, tensorCoeffSecond v i l y * inverseHessian v l j y)) k x = _
    rw [coordDeriv_add, coordDeriv_add, coordDeriv_add, coordDeriv_add]
    all_goals fun_prop
  rw [he]
  apply le_trans ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (hprod hd0 hb0 i j) hprodD)) hs1)) hs2)) hs3))
  change C * (S + Q) + C * (diffuseDefect v x + 2 * n * S) + n * (C * (S + Q)) +
    n * (C * (S + Q)) + n * (C * (S + Q)) ≤ C * (1 + 5 * n) * (diffuseDefect v x + S + Q)
  have hh : 0 ≤ C * (5 * n * diffuseDefect v x + 2 * n * Q) := by positivity
  nlinarith

lemma fderiv_diffuseDrift_sum {n : ℕ} (v f : Space n → ℝ) (x : Space n) :
    fderiv ℝ f x (diffuseDrift v x) = ∑ k : Fin n, driftCoeff v k x * coordDeriv f k x := by
  rw [fderiv_diffuseDrift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _; dsimp [driftCoeff]; ring

end DeGiorgi
end

end OAI
