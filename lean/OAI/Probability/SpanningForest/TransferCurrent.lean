import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Problem336.TransferCurrent

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : TopologicalSpace (Matrix n n ℝ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

def bilinear (M : Matrix n n ℝ) (a b : n → ℝ) : ℝ :=
  a ⬝ᵥ (M *ᵥ b)

omit [DecidableEq n] in
lemma bilinear_symmetric {M : Matrix n n ℝ} (hM : Mᵀ = M) (a b : n → ℝ) :
    bilinear M a b = bilinear M b a := by
  simpa [bilinear, hM] using Matrix.dotProduct_transpose_mulVec M a b

lemma inverse_symmetric {M : Matrix n n ℝ} (hM : Mᵀ = M) :
    (M⁻¹)ᵀ = M⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hM]

omit [DecidableEq n] in
lemma bilinear_rankOne (M : Matrix n n ℝ) (a b : n → ℝ) :
    bilinear (M * Matrix.vecMulVec b b * M) a a =
      bilinear M a b * bilinear M b a := by
  simp [bilinear, ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.mulVec_smul, dotProduct_smul, op_smul_eq_smul, mul_comm]

def bilinearCLM (a b : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => bilinear M a b
      map_add' := by
        intro M N
        simp [bilinear, Matrix.add_mulVec, dotProduct_add]
      map_smul' := by
        intro c M
        simp [bilinear, Matrix.smul_mulVec, dotProduct_smul] }

@[simp] lemma bilinearCLM_apply (a b : n → ℝ) (M : Matrix n n ℝ) :
    bilinearCLM a b M = bilinear M a b := rfl

lemma hasDerivAt_inverse_affine (M D : Matrix n n ℝ) (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => (M + t • D)⁻¹) (- (M⁻¹ * D * M⁻¹)) 0 := by
  rcases hM with ⟨u, rfl⟩
  have hline : HasDerivAt (fun t : ℝ => (u : Matrix n n ℝ) + t • D) D 0 := by
    simpa only [Function.id_def, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add (u : Matrix n n ℝ)
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hcomp := hinv.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  simpa [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.coe_units_inv] using hcomp

omit [DecidableEq n] in
lemma bilinear_neg (M : Matrix n n ℝ) (a b : n → ℝ) :
    bilinear (-M) a b = -bilinear M a b := by
  simp [bilinear, Matrix.neg_mulVec]

omit [DecidableEq n] in
lemma bilinear_smul (c : ℝ) (M : Matrix n n ℝ) (a b : n → ℝ) :
    bilinear (c • M) a b = c * bilinear M a b := by
  simp [bilinear, Matrix.smul_mulVec, dotProduct_smul]

lemma hasDerivAt_bilinear_inverse_affine (M D : Matrix n n ℝ)
    (hM : IsUnit M) (a b : n → ℝ) :
    HasDerivAt (fun t : ℝ => bilinear (M + t • D)⁻¹ a b)
      (-bilinear (M⁻¹ * D * M⁻¹) a b) 0 := by
  have h := (bilinearCLM a b).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_inverse_affine M D hM)
  simpa only [Function.comp_def, bilinearCLM_apply, bilinear_neg] using h

lemma hasDerivAt_transfer_rankOne (M : Matrix n n ℝ)
    (hM : IsUnit M) (hs : Mᵀ = M) (a b : n → ℝ) (ce cf : ℝ) :
    HasDerivAt (fun t : ℝ => ce * bilinear (M + t • (cf • Matrix.vecMulVec b b))⁻¹ a a)
      (-(ce * cf * (bilinear M⁻¹ a b)^2)) 0 := by
  have h := (hasDerivAt_bilinear_inverse_affine M (cf • Matrix.vecMulVec b b)
    hM a a).const_mul ce
  have hval : ce * -bilinear (M⁻¹ * (cf • Matrix.vecMulVec b b) * M⁻¹) a a =
      -(ce * cf * (bilinear M⁻¹ a b)^2) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, bilinear_smul, bilinear_rankOne]
    rw [bilinear_symmetric (inverse_symmetric hs) b a]
    ring
  rw [hval] at h
  exact h

lemma transfer_response_nonpos (M : Matrix n n ℝ) (a b : n → ℝ)
    {ce cf : ℝ} (he : 0 ≤ ce) (hf : 0 ≤ cf) :
    -(ce * cf * (bilinear M⁻¹ a b)^2) ≤ 0 := by
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg he hf) (sq_nonneg _))

lemma hasDerivAt_transfer_logWeight (M : Matrix n n ℝ)
    (hM : IsUnit M) (hs : Mᵀ = M) (a b : n → ℝ) (ce cf : ℝ) :
    HasDerivAt
      (fun t : ℝ => ce * bilinear
        (M + (Real.exp t - 1) • (cf • Matrix.vecMulVec b b))⁻¹ a a)
      (-(ce * cf * (bilinear M⁻¹ a b)^2)) 0 := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp t - 1) 1 0 := by
    simpa using (Real.hasDerivAt_exp (0 : ℝ)).sub_const 1
  have h := (hasDerivAt_transfer_rankOne M hM hs a b ce cf).comp_of_eq
    (0 : ℝ) hexp (by simp)
  simpa only [Function.comp_def, mul_one] using h

lemma hasDerivAt_transfer_logWeight_self (M : Matrix n n ℝ)
    (hM : IsUnit M) (hs : Mᵀ = M) (a : n → ℝ) (c : ℝ) :
    HasDerivAt
      (fun t : ℝ => Real.exp t *
        (c * bilinear (M + (Real.exp t - 1) • (c • Matrix.vecMulVec a a))⁻¹ a a))
      ((c * bilinear M⁻¹ a a) * (1 - c * bilinear M⁻¹ a a)) 0 := by
  have h := (Real.hasDerivAt_exp (0 : ℝ)).mul
    (hasDerivAt_transfer_logWeight M hM hs a a c c)
  simp only [Real.exp_zero, sub_self, zero_smul, add_zero, one_mul] at h
  have hval : c * bilinear M⁻¹ a a + -(c * c * (bilinear M⁻¹ a a)^2) =
      (c * bilinear M⁻¹ a a) * (1 - c * bilinear M⁻¹ a a) := by ring
  rw [hval] at h
  exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def laplacian (a : ι → n → ℝ) (h : ι → ℝ) : Matrix n n ℝ :=
  ∑ i, Real.exp (h i) • Matrix.vecMulVec (a i) (a i)

def shift (h : ι → ℝ) (f : ι) (t : ℝ) : ι → ℝ :=
  fun i => h i + if i = f then t else 0

omit [Fintype n] [DecidableEq n] [DecidableEq ι] in
lemma laplacian_symmetric (a : ι → n → ℝ) (h : ι → ℝ) :
    (laplacian a h)ᵀ = laplacian a h := by
  simp [laplacian, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

omit [Fintype n] [DecidableEq n] in
lemma laplacian_shift (a : ι → n → ℝ) (h : ι → ℝ) (f : ι) (t : ℝ) :
    laplacian a (shift h f t) = laplacian a h +
      (Real.exp t - 1) • (Real.exp (h f) • Matrix.vecMulVec (a f) (a f)) := by
  have hterm (i : ι) :
      Real.exp (shift h f t i) • Matrix.vecMulVec (a i) (a i) =
        Real.exp (h i) • Matrix.vecMulVec (a i) (a i) +
          if i = f then
            (Real.exp t - 1) • (Real.exp (h f) • Matrix.vecMulVec (a f) (a f))
          else 0 := by
    by_cases hi : i = f
    · subst i
      simp only [shift, ite_true, Real.exp_add, smul_smul]
      rw [← add_smul]
      congr 1
      ring
    · simp [shift, hi]
  simp only [laplacian, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

def marginal (a : ι → n → ℝ) (h : ι → ℝ) (e : ι) : ℝ :=
  Real.exp (h e) * bilinear (laplacian a h)⁻¹ (a e) (a e)

lemma hasDerivAt_marginal_shift_of_ne (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) {e f : ι} (hef : e ≠ f) :
    HasDerivAt (fun t : ℝ => marginal a (shift h f t) e)
      (-(Real.exp (h e) * Real.exp (h f) *
        (bilinear (laplacian a h)⁻¹ (a e) (a f))^2)) 0 := by
  simpa only [marginal, laplacian_shift, shift, ite_eq_right hef, add_zero] using
    hasDerivAt_transfer_logWeight (laplacian a h) hL (laplacian_symmetric a h)
      (a e) (a f) (Real.exp (h e)) (Real.exp (h f))

lemma hasDerivAt_marginal_shift_self (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    HasDerivAt (fun t : ℝ => marginal a (shift h e t) e)
      (marginal a h e * (1 - marginal a h e)) 0 := by
  simpa only [marginal, laplacian_shift, shift, ite_true, Real.exp_add,
    mul_assoc, mul_comm (Real.exp (h e)) (Real.exp _)] using
    hasDerivAt_transfer_logWeight_self (laplacian a h) hL (laplacian_symmetric a h)
      (a e) (Real.exp (h e))

lemma deriv_marginal_shift_nonpos (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) {e f : ι} (hef : e ≠ f) :
    deriv (fun t : ℝ => marginal a (shift h f t) e) 0 ≤ 0 := by
  rw [(hasDerivAt_marginal_shift_of_ne a h hL hef).deriv]
  exact transfer_response_nonpos _ _ _ (Real.exp_pos _).le (Real.exp_pos _).le

omit [DecidableEq ι] in

lemma sum_weighted_transfer_sq (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    (∑ f, Real.exp (h f) * (bilinear (laplacian a h)⁻¹ (a e) (a f))^2) =
      bilinear (laplacian a h)⁻¹ (a e) (a e) := by
  let M := laplacian a h
  have hs : (M⁻¹)ᵀ = M⁻¹ := inverse_symmetric (laplacian_symmetric a h)
  have hterm (f : ι) :
      Real.exp (h f) * (bilinear M⁻¹ (a e) (a f))^2 =
      bilinear (M⁻¹ * (Real.exp (h f) • Matrix.vecMulVec (a f) (a f)) * M⁻¹)
        (a e) (a e) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, bilinear_smul, bilinear_rankOne,
      bilinear_symmetric hs (a f) (a e)]
    ring
  change (∑ f, Real.exp (h f) * (bilinear M⁻¹ (a e) (a f))^2) = _
  simp_rw [hterm]
  have hsum := map_sum (bilinearCLM (a e) (a e))
    (fun f => M⁻¹ * (Real.exp (h f) • Matrix.vecMulVec (a f) (a f)) * M⁻¹)
    Finset.univ
  simp only [bilinearCLM_apply] at hsum
  rw [← hsum, ← Matrix.sum_mul, ← Matrix.mul_sum]
  change bilinear (M⁻¹ * M * M⁻¹) (a e) (a e) = bilinear M⁻¹ (a e) (a e)
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL), Matrix.one_mul]

def responseSquare (a : ι → n → ℝ) (h : ι → ℝ) (e f : ι) : ℝ :=
  Real.exp (h e) * Real.exp (h f) *
    (bilinear (laplacian a h)⁻¹ (a e) (a f))^2

omit [DecidableEq ι] in
lemma responseSquare_nonneg (a : ι → n → ℝ) (h : ι → ℝ) (e f : ι) :
    0 ≤ responseSquare a h e f := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (sq_nonneg _)

omit [DecidableEq ι] in
lemma responseSquare_self (a : ι → n → ℝ) (h : ι → ℝ) (e : ι) :
    responseSquare a h e e = (marginal a h e)^2 := by
  unfold responseSquare marginal
  ring

omit [DecidableEq ι] in
lemma sum_responseSquare (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    ∑ f, responseSquare a h e f = marginal a h e := by
  have hs := congrArg (fun x : ℝ => Real.exp (h e) * x)
    (sum_weighted_transfer_sq a h hL e)
  simpa only [Finset.mul_sum, marginal, responseSquare, mul_assoc] using hs

omit [DecidableEq ι] in
lemma marginal_nonneg (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) : 0 ≤ marginal a h e := by
  rw [← sum_responseSquare a h hL e]
  exact Finset.sum_nonneg (fun f _ => responseSquare_nonneg a h e f)

omit [DecidableEq ι] in
lemma marginal_le_one (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) : marginal a h e ≤ 1 := by
  have hsq : responseSquare a h e e ≤ ∑ f, responseSquare a h e f :=
    Finset.single_le_sum (fun f _ => responseSquare_nonneg a h e f) (Finset.mem_univ e)
  rw [sum_responseSquare a h hL e, responseSquare_self] at hsq
  nlinarith [sq_nonneg (marginal a h e - 1)]

def response (a : ι → n → ℝ) (h : ι → ℝ) (e f : ι) : ℝ :=
  (if e = f then marginal a h e else 0) - responseSquare a h e f

lemma response_self (a : ι → n → ℝ) (h : ι → ℝ) (e : ι) :
    response a h e e = marginal a h e * (1 - marginal a h e) := by
  simp only [response, ite_true, responseSquare_self]
  ring

lemma response_ne_nonpos (a : ι → n → ℝ) (h : ι → ℝ)
    {e f : ι} (hef : e ≠ f) : response a h e f ≤ 0 := by
  simp only [response, ite_eq_right hef, zero_sub]
  exact neg_nonpos.mpr (responseSquare_nonneg a h e f)

lemma hasDerivAt_marginal_shift (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e f : ι) :
    HasDerivAt (fun t : ℝ => marginal a (shift h f t) e) (response a h e f) 0 := by
  by_cases hef : e = f
  · subst f
    rw [response_self]
    exact hasDerivAt_marginal_shift_self a h hL e
  · simpa only [response, ite_eq_right hef, zero_sub, responseSquare] using
      hasDerivAt_marginal_shift_of_ne a h hL hef

lemma sum_response (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) : ∑ f, response a h e f = 0 := by
  simp only [response, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, sum_responseSquare a h hL e, sub_self]

lemma sum_abs_response (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    ∑ f, |response a h e f| = 2 * marginal a h e * (1 - marginal a h e) := by
  have hd : 0 ≤ response a h e e := by
    rw [response_self]
    exact mul_nonneg (marginal_nonneg a h hL e)
      (sub_nonneg.mpr (marginal_le_one a h hL e))
  have habs (f : ι) : |response a h e f| =
      (if e = f then 2 * response a h e e else 0) - response a h e f := by
    by_cases hef : e = f
    · subst f
      rw [ite_eq_left rfl, abs_of_nonneg hd]
      ring
    · rw [ite_eq_right hef, zero_sub, abs_of_nonpos (response_ne_nonpos a h hef)]
  simp_rw [habs]
  rw [Finset.sum_sub_distrib, sum_response a h hL e]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_zero]
  rw [response_self]
  ring

lemma sum_abs_deriv_marginal_le_half (a : ι → n → ℝ) (h : ι → ℝ)
    (hL : IsUnit (laplacian a h)) (e : ι) :
    (∑ f, |deriv (fun t : ℝ => marginal a (shift h f t) e) 0|) ≤ (1 : ℝ) / 2 := by
  simp_rw [(hasDerivAt_marginal_shift a h hL e _).deriv]
  rw [sum_abs_response a h hL e]
  nlinarith [sq_nonneg (marginal a h e - 1 / 2)]

end Problem336.TransferCurrent

end

end OAI
