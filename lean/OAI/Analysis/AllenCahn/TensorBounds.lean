import OAI.Analysis.AllenCahn.TensorCalculus

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff
open Filter Topology

lemma hessianSquare_drift_identity {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (x : Space n) :
    Laplacian.laplacian (hessianSquare v) x - fderiv ℝ (hessianSquare v) x (diffuseDrift v x) =
      ∑ i : Fin n, ∑ j : Fin n, (2 * ‖gradient (inverseHessian v i j) x‖ ^ 2 +
        2 * inverseHessian v i j x * (Laplacian.laplacian (inverseHessian v i j) x -
          fderiv ℝ (inverseHessian v i j) x (diffuseDrift v x))) := by
  have hT (i j : Fin n) : ContDiff ℝ 2 (inverseHessian v i j) :=
    smooth_C2 (inverseHessian_smooth hv hi i j)
  have he : hessianSquare v = fun y => ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j y ^ 2 :=
    funext (hessianSquare_eq_sum v)
  rw [he, laplacian_sum _ (fun i _ => ContDiff.sum (fun j _ => (hT i j).pow 2))]
  rw [fderiv_fun_sum (A := fun i y => ∑ j : Fin n, inverseHessian v i j y ^ 2)
    (fun i _ => DifferentiableAt.fun_sum
    (fun j _ => ((hT i j).differentiable (by norm_num) x).fun_pow 2))]
  simp only [sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [laplacian_sum _ (fun j _ => (hT i j).pow 2),
    fderiv_fun_sum (A := fun j y => inverseHessian v i j y ^ 2)
      (fun j _ => ((hT i j).differentiable (by norm_num) x).fun_pow 2)]
  simp only [sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact drift_square_identity (hT i j) (diffuseDrift v) x

def tensorSystemConstant (n : ℕ) : ℝ :=
  2 + 4 * n + 4 * n * (12 * (2 * Real.sqrt 2 + 1))

def tensorBernsteinConstant (n : ℕ) : ℝ := 1 + 2 * n ^ 2 * tensorSystemConstant n ^ 2

lemma hessianSquare_drift_lower {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    -tensorBernsteinConstant n * (hessianSquare v x + diffuseDefect v x ^ 2) ≤
      Laplacian.laplacian (hessianSquare v) x - fderiv ℝ (hessianSquare v) x (diffuseDrift v x) := by
  let C := tensorSystemConstant n
  let S := Real.sqrt (hessianSquare v x)
  have hC : 0 ≤ C := by dsimp [C, tensorSystemConstant]; positivity
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = hessianSquare v x := Real.sq_sqrt (hessianSquare_nonneg v x)
  have hD : 0 ≤ diffuseDefect v x := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hpair (i j : Fin n) :
      -(inverseHessian v i j x ^ 2) - 2 * C ^ 2 * (hessianSquare v x + diffuseDefect v x ^ 2) ≤
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
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hessianSquare_eq_sum]
  dsimp only [tensorBernsteinConstant]
  change -(1 + 2 * (n : ℝ) ^ 2 * C ^ 2) * (hessianSquare v x + diffuseDefect v x ^ 2) ≤ _
  nlinarith [sq_nonneg (diffuseDefect v x)]

lemma diffuseDefect_drift_upper {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    Laplacian.laplacian (diffuseDefect v) x - fderiv ℝ (diffuseDefect v) x (diffuseDrift v x) ≤
      2 * diffuseDefect v x - 2 * hessianSquare v x := by
  rw [diffuseDefect_laplacian hv hi hAC]
  have hD := diffuseDefect_nonneg (smooth_C2 hv) hi hAC x
  have hp := inverseProfile_gradient_bound (smooth_C2 hv) hi hAC x
  have hp0 := norm_nonneg (gradient (inverseProfile v) x)
  have hp2 : ‖gradient (inverseProfile v) x‖ ^ 2 ≤ 1 := by nlinarith
  have hq : defectWeight v x ≤ 1 := by dsimp [defectWeight]; nlinarith [sq_nonneg (v x)]
  have hq0 : 0 ≤ defectWeight v x := (weight_pos (hi x)).le
  have hh := mul_le_mul hq hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hfinal := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * diffuseDefect v x by positivity)
  rw [diffuseDrift, map_smul, smul_eq_mul, ← inner_gradient_left, real_inner_comm]
  dsimp only [hessianSquare]
  nlinarith

theorem hessianSquare_le_defect {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (x : Space n) :
    hessianSquare v x ≤ (tensorBernsteinConstant n + 3) * diffuseDefect v x := by
  have hC : 0 ≤ tensorBernsteinConstant n := by dsimp [tensorBernsteinConstant]; positivity
  have H := quotient_bernstein
    (smooth_C2 (hessianSquare_smooth hv hi)) (smooth_C2 (diffuseDefect_smooth hv hi)) (diffuseDrift v)
    (show 0 ≤ (n : ℝ) * (12 * (2 * Real.sqrt 2 + 1)) ^ 2 by positivity)
    (show 0 ≤ 2 * Real.sqrt 2 by positivity)
    (show 0 ≤ 2 * (n : ℝ) ^ 2 * (12 * (2 * Real.sqrt 2 + 1)) by positivity)
    hC (by norm_num : (0 : ℝ) ≤ 2)
    (fun y => ⟨hessianSquare_nonneg v y, hessianSquare_uniform_bound hv hi hAC y⟩)
    (fun y => ⟨diffuseDefect_nonneg (smooth_C2 hv) hi hAC y, diffuseDefect_le_one v y⟩)
    (diffuseDrift_bound (smooth_C2 hv) hi hAC) (diffuseDefect_gradient_uniform_bound hv hi hAC)
    (hessianSquare_drift_lower hv hi hAC) (diffuseDefect_drift_upper hv hi hAC) x
  convert H using 1
  ring

lemma quotient_bernstein_linear {n : ℕ} {f d : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hd : ContDiff ℝ 2 d) (b : Space n → Space n)
    {M B G A c : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hdb : ∀ x, 0 ≤ d x ∧ d x ≤ 1)
    (hbb : ∀ x, ‖b x‖ ≤ B) (hgb : ∀ x, ‖gradient d x‖ ≤ G)
    (hfde : ∀ x, -A * (f x + d x) ≤
      Laplacian.laplacian f x - fderiv ℝ f x (b x))
    (hdde : ∀ x, Laplacian.laplacian d x - fderiv ℝ d x (b x) ≤ c * d x - 2 * f x) :
    ∀ x, f x ≤ (A + c + 1) * d x := by
  have hδ {δ : ℝ} (hδ : 0 < δ) (x : Space n) : f x ≤ (A + c + 1) * (d x + δ) := by
    let e := fun y => d y + δ
    let w := fun y => f y / e y
    let b' := fun y => b y - (2 / e y) • gradient d y
    have he : ContDiff ℝ 2 e := hd.add contDiff_const
    have hep (y : Space n) : 0 < e y := by dsimp [e]; linarith [(hdb y).1]
    have heδ (y : Space n) : δ ≤ e y := by dsimp [e]; linarith [(hdb y).1]
    have hw : ContDiff ℝ 2 w := hf.div he (fun y => (hep y).ne')
    have hwe (y : Space n) : w y * e y = f y := by dsimp [w]; field_simp [(hep y).ne']
    have hwp (y : Space n) : 0 ≤ w y := div_nonneg (hfb y).1 (hep y).le
    have hwb (y : Space n) : |w y| ≤ M / δ := by
      rw [abs_of_nonneg (hwp y)]
      exact div_le_div₀ hM (hfb y).2 hδ (heδ y)
    have hb'b (y : Space n) : ‖b' y‖ ≤ B + 2 / δ * G := by
      calc ‖b' y‖ ≤ ‖b y‖ + ‖(2 / e y) • gradient d y‖ := norm_sub_le _ _
           _ = ‖b y‖ + 2 / e y * ‖gradient d y‖ := by
             rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) (hep y))]
           _ ≤ B + 2 / δ * G := add_le_add (hbb y)
             (mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hδ (heδ y)) (hgb y)
               (norm_nonneg _) (by positivity))
    have hele (y : Space n) : Laplacian.laplacian e y = Laplacian.laplacian d y := by
      rw [laplacian_fun_add hd contDiff_const]
      simp
    have hef (y : Space n) : fderiv ℝ e y = fderiv ℝ d y := by
      dsimp [e]
      rw [fderiv_fun_add (hd.differentiable (by norm_num) y) (differentiableAt_const δ)]
      simp
    have heg (y : Space n) : gradient e y = gradient d y := by simp only [gradient, hef]
    have hwde (y : Space n) : w y ^ 2 - (A + c) * w y - (A + c) ≤
        Laplacian.laplacian w y - fderiv ℝ w y (b' y) := by
      have hI := drift_quotient_identity hf he (fun z => (hep z).ne') b y
      change e y * (Laplacian.laplacian w y -
          fderiv ℝ w y (b y - (2 / e y) • gradient e y)) = _ - w y * _ at hI
      rw [heg, hele, hef] at hI
      have h₁ := hfde y
      have h₂ := mul_le_mul_of_nonneg_left (hdde y) (hwp y)
      have h₃ : d y ≤ e y := by dsimp [e]; linarith
      have h₄ : c * w y * d y ≤ c * w y * e y :=
        mul_le_mul_of_nonneg_left (by dsimp [e]; linarith) (mul_nonneg hc (hwp y))
      have h₅ := mul_le_mul_of_nonneg_left h₃ hA
      have h₆ : 0 ≤ w y ^ 2 * e y := mul_nonneg (sq_nonneg _) (hep y).le
      have h₇ : 0 ≤ c * e y := mul_nonneg hc (hep y).le
      apply (mul_le_mul_iff_right₀ (hep y)).mp
      dsimp only [b']
      rw [← hwe y] at h₁ h₂
      nlinarith
    have hh := bounded_drift_logistic hw b'
      (show 0 ≤ M / δ by positivity) (show 0 ≤ B + 2 / δ * G by positivity)
      (add_nonneg hA hc) hwb hb'b hwde x
    have hh' := mul_le_mul_of_nonneg_right hh (hep x).le
    rw [hwe] at hh'
    exact hh'
  intro x
  by_contra h
  have hh : 0 < f x - (A + c + 1) * d x := sub_pos.mpr (lt_of_not_ge h)
  let δ := (f x - (A + c + 1) * d x) / (2 * (A + c + 1))
  have hK : 0 < A + c + 1 := by linarith
  have hδp : 0 < δ := div_pos hh (by linarith)
  have hh' := hδ hδp x
  dsimp [δ] at hh'
  have hrel : (A + c + 1) * ((f x - (A + c + 1) * d x) / (2 * (A + c + 1))) =
      (f x - (A + c + 1) * d x) / 2 := by field_simp
  rw [mul_add, hrel] at hh'
  linarith

def C1Bound {n : ℕ} (f : Space n → ℝ) (C : ℝ) : Prop :=
  (∀ x, |f x| ≤ C) ∧ ∀ i x, |coordDeriv f i x| ≤ C

lemma C1Bound.mono {n : ℕ} {f : Space n → ℝ} {C K : ℝ}
    (h : C1Bound f C) (hCK : C ≤ K) : C1Bound f K :=
  ⟨fun x => (h.1 x).trans hCK, fun i x => (h.2 i x).trans hCK⟩

lemma C1Bound.const {n : ℕ} (c : ℝ) : C1Bound (fun _ : Space n => c) |c| := by
  constructor
  · intro x; rfl
  · intro i x; simp [coordDeriv]

lemma C1Bound.neg {n : ℕ} {f : Space n → ℝ} {C : ℝ}
    (hf : Differentiable ℝ f) (h : C1Bound f C) : C1Bound (fun x => -f x) C := by
  constructor
  · intro x; simpa using h.1 x
  · intro i x
    change |fderiv ℝ (-f) x (basis n i)| ≤ C
    rw [(hf x).hasFDerivAt.neg.fderiv]
    simpa only [neg_apply, abs_neg, coordDeriv] using h.2 i x

lemma C1Bound.mul {n : ℕ} {f g : Space n → ℝ} {C K : ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (h : C1Bound f C) (h' : C1Bound g K) :
    C1Bound (fun x => f x * g x) (2 * C * K) := by
  constructor
  · intro x
    rw [abs_mul]
    have hh := mul_le_mul (h.1 x) (h'.1 x) (abs_nonneg _) hC
    nlinarith
  · intro i x
    rw [coordDeriv_mul hf hg]
    calc |f x * coordDeriv g i x + g x * coordDeriv f i x| ≤
        |f x * coordDeriv g i x| + |g x * coordDeriv f i x| := abs_add_le _ _
      _ ≤ C * K + K * C := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (h.1 x) (h'.2 i x) (abs_nonneg _) hC)
          (mul_le_mul (h'.1 x) (h.2 i x) (abs_nonneg _) hK)
      _ = _ := by ring

lemma C1Bound.const_mul {n : ℕ} {f : Space n → ℝ} {C : ℝ}
    (hf : Differentiable ℝ f) (_hC : 0 ≤ C) (h : C1Bound f C) (a : ℝ) :
    C1Bound (fun x => a * f x) (|a| * C) := by
  constructor
  · intro x; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.1 x) (abs_nonneg _)
  · intro i x
    change |fderiv ℝ (fun x => a * f x) x (basis n i)| ≤ _
    rw [fderiv_const_mul (hf x)]
    simp only [smul_apply, smul_eq_mul, abs_mul]
    change |a| * |coordDeriv f i x| ≤ _
    exact mul_le_mul_of_nonneg_left (h.2 i x) (abs_nonneg _)

lemma inverseHessian_gradient_uniform_bound {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (i j : Fin n) (x : Space n) :
    ‖gradient (inverseHessian v i j) x‖ ≤
      2 * (2 * (12 * (2 * Real.sqrt 2 + 1)) +
        tensorSystemConstant n * (1 + (n + 1) * (12 * (2 * Real.sqrt 2 + 1))) + 3) *
        (2 * Real.sqrt 2 + 1) := by
  let K := 12 * (2 * Real.sqrt 2 + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ tensorSystemConstant n := by dsimp [tensorSystemConstant]; positivity
  apply PoissonSupport.DeGiorgi.bounded_drift_gradient
    (smooth_C2 (inverseHessian_smooth hv hi i j)) (diffuseDrift v) hK (by positivity)
    (by positivity) (inverseHessian_abs_le hv hi hAC i j) (diffuseDrift_bound (smooth_C2 hv) hi hAC)
  intro y
  apply (inverseHessian_drift_abs_bound hv hi hAC i j y).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add (diffuseDefect_le_one v y)
  have hs := Real.sq_sqrt (hessianSquare_nonneg v y)
  have hh := hessianSquare_uniform_bound hv hi hAC y
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk : 0 ≤ (n + 1 : ℝ) * K := by positivity
  have hmul : (n : ℝ) * K ^ 2 ≤ ((n + 1 : ℝ) * K) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg K), mul_nonneg hn (sq_nonneg K)]
  change hessianSquare v y ≤ (n : ℝ) * K ^ 2 at hh
  nlinarith [Real.sqrt_nonneg (hessianSquare v y)]

def inverseJetConstant (n : ℕ) : ℝ :=
  1 + 12 * (2 * Real.sqrt 2 + 1) +
    2 * (n : ℝ) * (12 * (2 * Real.sqrt 2 + 1)) +
    2 * (2 * (12 * (2 * Real.sqrt 2 + 1)) +
      tensorSystemConstant n * (1 + (n + 1) * (12 * (2 * Real.sqrt 2 + 1))) + 3) *
      (2 * Real.sqrt 2 + 1)

lemma inverseJetConstant_one_le (n : ℕ) : 1 ≤ inverseJetConstant n := by
  change 1 ≤ 1 + _ + _ + _
  have ha : 0 ≤ 12 * (2 * Real.sqrt 2 + 1) := by positivity
  have hb : 0 ≤ 2 * (n : ℝ) * (12 * (2 * Real.sqrt 2 + 1)) := by positivity
  have hc : 0 ≤ tensorSystemConstant n := by dsimp [tensorSystemConstant]; positivity
  have hd : 0 ≤ 2 * (2 * (12 * (2 * Real.sqrt 2 + 1)) +
    tensorSystemConstant n * (1 + (n + 1) * (12 * (2 * Real.sqrt 2 + 1))) + 3) *
    (2 * Real.sqrt 2 + 1) := by positivity
  linarith

end DeGiorgi
end

end OAI
