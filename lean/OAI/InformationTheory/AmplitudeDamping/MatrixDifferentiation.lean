import OAI.InformationTheory.AmplitudeDamping.Channel

namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- The determinant as a continuous multilinear map in its rows. -/
def detMultilinear : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ι → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := by
      change Continuous (Matrix.det : Matrix ι ι ℂ → ℂ)
      fun_prop }

/-- Jacobi's differential, without an invertibility assumption. -/
theorem det_linearDeriv (A H : Matrix ι ι ℂ) :
    detMultilinear.linearDeriv A H = Matrix.trace (H * A.adjugate) := by
  change (detMultilinear.linearDeriv (fun i j ↦ A i j)) (fun i j ↦ H i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (A.updateRow i (H i)).det = _
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Jacobi's formula along any differentiable complex-matrix curve. -/
theorem hasDerivAt_det {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    HasDerivAt (fun s ↦ (A s).det) (Matrix.trace (H * (A t).adjugate)) t := by
  have h := ((detMultilinear.hasFDerivAt (A t)).restrictScalars ℝ).comp_hasDerivAt t hA
  change HasDerivAt (fun s ↦ (A s).det) (detMultilinear.linearDeriv (A t) H) t at h
  rwa [det_linearDeriv] at h

omit [DecidableEq ι] in
/-- Product differentiation with the entrywise matrix topology. -/
theorem hasDerivAt_matrix_mul {A B : ℝ → Matrix ι ι ℂ}
    {H K : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hB : HasDerivAt B K t) :
    HasDerivAt (fun s ↦ A s * B s) (H * B t + A t * K) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hh := HasDerivAt.sum (u := Finset.univ) (fun k _ ↦
    ((hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) k).mul
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB k) j)))
  convert! hh using 1
  · ext s
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, Finset.sum_add_distrib]

/-- The row replacement operation is affine. -/
theorem hasDerivAt_updateRow {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (i : ι) (x : ι → ℂ) :
    HasDerivAt (fun s ↦ (A s).updateRow i x) (H.updateRow i 0) t := by
  apply hasDerivAt_pi.2
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hasDerivAt_const t x
  · simpa [Matrix.updateRow_ne hj] using hasDerivAt_pi.1 hA j

/-- Polynomial differentiability of the adjugate, with no nonsingularity restriction. -/
theorem differentiableAt_adjugate {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    DifferentiableAt ℝ (fun s ↦ (A s).adjugate) t := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  simpa only [Matrix.adjugate_apply] using
    (hasDerivAt_det (hasDerivAt_updateRow hA j (Pi.single i 1))).differentiableAt

/-- The full noncommutative derivative of matrix inversion. -/
theorem hasDerivAt_matrix_inv {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ (A s)⁻¹) (-(A t)⁻¹ * H * (A t)⁻¹) t := by
  have hd := (hasDerivAt_det hA).differentiableAt.inv hdet
  have hi : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹) t := by
    convert! hd.smul (differentiableAt_adjugate hA) using 1
    ext s
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  have hev := (hasDerivAt_det hA).continuousAt.eventually_ne hdet
  have hc : HasDerivAt (fun s ↦ A s * (A s)⁻¹) 0 t :=
    (hasDerivAt_const t (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq
      (hev.mono fun s hs ↦ Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hs))
  have hh := (hasDerivAt_matrix_mul hA hi.hasDerivAt).unique hc
  have he := congrArg (fun M ↦ (A t)⁻¹ * M) hh
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul, Matrix.mul_zero] at he
  have hk := eq_neg_of_add_eq_zero_right he
  convert! hi.hasDerivAt using 1
  simp only [hk, Matrix.neg_mul]

/-- Logarithmic norm differentiation, without choosing a complex logarithm branch. -/
theorem hasDerivAt_log_norm_of_mul {z : ℝ → ℂ} {w : ℂ} {t : ℝ}
    (hz : HasDerivAt z (z t * w) t) (h0 : z t ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖z s‖) w.re t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  change HasDerivAt (fun s ↦ (z s).re) (z t * w).re t at hr
  change HasDerivAt (fun s ↦ (z s).im) (z t * w).im t at hi
  have hq : HasDerivAt (fun s ↦ Complex.normSq (z s))
      (2 * Complex.normSq (z t) * w.re) t := by
    convert! (hr.mul hr).add (hi.mul hi) using 1
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hn : Complex.normSq (z t) ≠ 0 := ne_of_gt (Complex.normSq_pos.2 h0)
  have h := (hq.log hn).div_const 2
  convert! h using 1
  · ext s
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    simp
  · field_simp

/-- Jacobi's formula for log absolute determinant, valid for every nonsingular complex matrix. -/
theorem hasDerivAt_logNormDet {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖(A s).det‖) (Matrix.trace (H * (A t)⁻¹)).re t := by
  have ha : (A t).adjugate = (A t).det • (A t)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  have h := hasDerivAt_det hA
  rw [ha, Matrix.mul_smul, Matrix.trace_smul] at h
  exact hasDerivAt_log_norm_of_mul h hdet

end GAD


open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Entrywise real trace bound, avoiding any norm convention for matrices. -/
theorem trace_square_re_le (B : Matrix ι ι ℂ) :
    (Matrix.trace (B * B)).re ≤ (Matrix.trace (B.conjTranspose * B)).re := by
  have he (z w : ℂ) : 2 * (z * w).re ≤ Complex.normSq z + Complex.normSq w := by
    simp only [Complex.mul_re, Complex.normSq_apply]
    nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im + w.im)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ he (B i j) (B j i)))
  have hs : (∑ i, ∑ j, Complex.normSq (B i j)) =
      ∑ i, ∑ j, Complex.normSq (B j i) := Finset.sum_comm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [hs] at hh
  have hb : (Matrix.trace (B.conjTranspose * B)).re =
      ∑ i, ∑ j, Complex.normSq (B j i) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.normSq_apply,
      Complex.mul_re, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [hb]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  linarith

/-- A skew-Hermitian perturbation of the identity is nonsingular. -/
theorem skew_one_add_isUnit (K : Matrix ι ι ℂ) (hK : K.conjTranspose = -K) :
    IsUnit (1 + K) := by
  have he : (1 + K).conjTranspose * (1 + K) = 1 + K.conjTranspose * K := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    noncomm_ring [hK]
  have hp : ((1 + K).conjTranspose * (1 + K)).PosDef := by
    rw [he]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self K)
  have hd := hp.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hd)

/-- The resolvent of a skew-Hermitian matrix is a contraction in quadratic-form order. -/
theorem skew_resolvent_contraction (K : Matrix ι ι ℂ) (hK : K.conjTranspose = -K) :
    (1 - ((1 + K)⁻¹).conjTranspose * (1 + K)⁻¹).PosSemidef := by
  let R := (1 + K)⁻¹
  have hd : IsUnit (1 + K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (skew_one_add_isUnit K hK)
  have hR : (1 + K) * R = 1 := Matrix.mul_nonsing_inv _ hd
  have hRt : R.conjTranspose * (1 + K).conjTranspose = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hR
  have he : (1 + K).conjTranspose * (1 + K) = 1 + K.conjTranspose * K := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    noncomm_ring [hK]
  have hh : R.conjTranspose * (1 + K.conjTranspose * K) * R = 1 := by
    rw [← he, ← Matrix.mul_assoc, hRt, Matrix.one_mul, hR]
  have hh' : 1 - R.conjTranspose * R = (K * R).conjTranspose * (K * R) := by
    rw [Matrix.conjTranspose_mul]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul] at hh
    apply sub_eq_iff_eq_add.2
    rw [← hh]
    noncomm_ring
  change (1 - R.conjTranspose * R).PosSemidef
  rw [hh']
  exact Matrix.posSemidef_conjTranspose_mul_self _


theorem skew_resolvent_trace_bound (K L : Matrix ι ι ℂ)
    (hK : K.conjTranspose = -K) (hL : L.IsHermitian) :
    (Matrix.trace (((1 + K)⁻¹ * L) * ((1 + K)⁻¹ * L))).re ≤
      (Matrix.trace (L * L)).re := by
  let R := (1 + K)⁻¹
  have hp := (skew_resolvent_contraction K hK).conjTranspose_mul_mul_same L
  have ht := hp.trace_nonneg
  have ht' := (Complex.nonneg_iff.mp ht).1
  have he : (L.conjTranspose * (1 - R.conjTranspose * R) * L).trace =
      (L * L).trace - ((R * L).conjTranspose * (R * L)).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub,
      Matrix.conjTranspose_mul, hL.eq]
    simp only [Matrix.mul_assoc]
  change 0 ≤ (Matrix.trace (L.conjTranspose * (1 - R.conjTranspose * R) * L)).re at ht'
  rw [he, Complex.sub_re] at ht'
  exact (trace_square_re_le (R * L)).trans (sub_nonneg.1 ht')

/-- The Hessian bound at an arbitrary positive definite base point. -/
theorem skew_shift_trace_bound (D Z H : Matrix ι ι ℂ)
    (hD : D.PosDef) (hZ : Z.conjTranspose = -Z) (hH : H.IsHermitian) :
    IsUnit (D + Z) ∧
      (Matrix.trace (((D + Z)⁻¹ * H) * ((D + Z)⁻¹ * H))).re ≤
        (Matrix.trace ((D⁻¹ * H) * (D⁻¹ * H))).re := by
  let S := CFC.sqrt D
  have hS : S * S = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hS.symm ▸ hD.isUnit)
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hSu
  have hSh : S.IsHermitian := (CFC.sqrt_nonneg D).posSemidef.isHermitian
  let W := S⁻¹
  have hW : W.IsHermitian := hSh.inv
  have hSW : S * W = 1 := Matrix.mul_nonsing_inv _ hSd
  have hWS : W * S = 1 := Matrix.nonsing_inv_mul _ hSd
  let K := W * Z * W
  have hK : K.conjTranspose = -K := by
    dsimp [K]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hW.eq, hZ]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hC : D + Z = S * (1 + K) * S := by
    dsimp [K]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS]
    congr 1
    simp only [← Matrix.mul_assoc, hSW, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hWS, Matrix.mul_one]
  have hCu : IsUnit (D + Z) := by
    rw [hC]
    exact (hSu.mul (skew_one_add_isUnit K hK)).mul hSu
  refine ⟨hCu, ?_⟩
  let R := (1 + K)⁻¹
  have hCi : (D + Z)⁻¹ = W * R * W := by
    rw [hC, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    exact (Matrix.mul_assoc _ _ _).symm
  have hDi : D⁻¹ = W * W := by rw [← hS, Matrix.mul_inv_rev]
  let L := W * H * W
  have hL : L.IsHermitian := by
    simpa only [hW.eq] using Matrix.isHermitian_conjTranspose_mul_mul W hH
  have heC : Matrix.trace (((D + Z)⁻¹ * H) * ((D + Z)⁻¹ * H)) =
      Matrix.trace ((R * L) * (R * L)) := by
    rw [hCi]
    dsimp [L]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm W (R * W * H * W * R * W * H)
  have heD : Matrix.trace ((D⁻¹ * H) * (D⁻¹ * H)) = Matrix.trace (L * L) := by
    rw [hDi]
    dsimp [L]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm W (W * H * W * W * H)
  rw [heC, heD]
  exact skew_resolvent_trace_bound K L hK hL

end GAD

end

end OAI
