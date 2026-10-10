import OAI.Analysis.Quantum.PPTSquare.TraceCompletion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]

omit [Fintype a] [Fintype c] in
lemma coord_compress [DecidableEq b] (e : a → b) (f : c → b) (X : Mat b) :
    (coord e)ᴴ * X * coord f = X.submatrix e f := by
  ext i j
  simp [coord, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    apply_ite, ite_mul]

omit [Fintype a] [Fintype c] in
lemma coord_inner [DecidableEq b] (e : a → b) (f : c → b) :
    (coord e)ᴴ * coord f = fun i j => if e i = f j then 1 else 0 := by
  ext i j
  simp [coord, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]

omit [Fintype a] in
lemma coord_isometry [DecidableEq a] [DecidableEq b] (e : a → b) (he : Function.Injective e) :
    (coord e)ᴴ * coord e = 1 := by
  rw [coord_inner]
  ext i j
  simp [Matrix.one_apply, he.eq_iff]

omit [Fintype a] [Fintype b] in
lemma coord_real [DecidableEq b] (e : a → b) (i : b) (j : a) : (coord e i j).im = 0 := by
  simp [coord, apply_ite]

omit [Fintype a] [Fintype b] in
lemma coord_transpose [DecidableEq b] (e : a → b) : (coord e)ᵀ = (coord e)ᴴ := by
  ext i j
  simp [coord, Matrix.conjTranspose_apply, Matrix.transpose_apply, apply_ite]

omit [Fintype b] in
lemma transpose_ad_coord [DecidableEq b] (e : a → b) (X : Mat a) :
    (ad (coord e) X)ᵀ = ad (coord e) Xᵀ := by
  simp only [ad_apply, Matrix.transpose_mul, ← coord_transpose, Matrix.transpose_transpose,
    Matrix.mul_assoc]

omit [Fintype b] in
lemma coord_single [DecidableEq a] [DecidableEq b] (e : a → b) (i j : a) :
    ad (coord e) (Matrix.single i j 1) = Matrix.single (e i) (e j) 1 := by
  ext x y
  have hmul (r : a) : (coord e * Matrix.single i j (1 : ℂ)) x r =
      if r = j then coord e x i else 0 := by
    by_cases hr : r = j
    · subst r
      simp
    · simp [hr, Matrix.mul_single_apply_of_ne]
  rw [ad_apply, Matrix.mul_apply]
  simp_rw [hmul]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [coord, Matrix.conjTranspose_apply, Matrix.single_apply, apply_ite, star_one, star_zero]
  by_cases hx : x = e i <;> by_cases hy : y = e j <;> simp [hx, hy, eq_comm]

omit [Fintype a] [Fintype b] [Fintype c] in
lemma coord_kronecker [DecidableEq b] {d : Type} [DecidableEq d]
    (e : a → b) (f : c → d) :
    coord e ⊗ₖ coord f = coord (fun x : a × c => (e x.1, f x.2)) := by
  ext ⟨x,y⟩ ⟨i,j⟩
  simp only [Matrix.kronecker_apply, coord, Prod.mk.injEq]
  by_cases hx : x = e i <;> by_cases hy : y = f j <;> simp [hx, hy]

@[simp] lemma W0_isometry (d : ℕ) : (W0 d)ᴴ * W0 d = 1 := by
  exact coord_isometry _ (by intro i j h; simpa [first] using h)

@[simp] lemma W1_isometry (d : ℕ) : (W1 d)ᴴ * W1 d = 1 := by
  exact coord_isometry _ (by intro i j h; simpa [second] using h)

@[simp] lemma W0_W1 (d : ℕ) : (W0 d)ᴴ * W1 d = 0 := by
  rw [W0, W1, coord_inner]
  ext i j
  simp [first, second]

@[simp] lemma W1_W0 (d : ℕ) : (W1 d)ᴴ * W0 d = 0 := by
  rw [W0, W1, coord_inner]
  ext i j
  simp [first, second]

@[simp] lemma W0_flag (d : ℕ) : (W0 d)ᴴ * flagProjection d * W0 d = 0 := by
  rw [W0, coord_compress]
  ext i j
  simp [flagProjection, first, flag]

@[simp] lemma W1_flag (d : ℕ) : (W1 d)ᴴ * flagProjection d * W1 d = 0 := by
  rw [W1, coord_compress]
  ext i j
  simp [flagProjection, second, flag]

@[simp] lemma flag_transpose (d : ℕ) : (flagProjection d)ᵀ = flagProjection d := by
  simp [flagProjection]

lemma dimension (d : ℕ) : Fintype.card (Space d) = 2 * d + 1 := by
  simp [Space]
  omega

end ChannelCompletion

namespace ChannelCompletion

lemma theta_decomposition (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    theta d F G =
      (coefficient G : ℂ) • ((ad (W0 d)).comp (G.comp (ad (W1 d)ᴴ))) +
      (coefficient F : ℂ) • ((ad (W1 d)).comp (F.comp (ad (W0 d)ᴴ))) +
      (measureFlag d (defect F)).comp (ad (W0 d)ᴴ) +
      (measureFlag d (defect G)).comp (ad (W1 d)ᴴ) +
      measureFlag d (flagProjection d) := by
  apply LinearMap.ext
  intro X
  simp only [theta, measureFlag, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    ad_apply, Matrix.conjTranspose_conjTranspose, add_smul]
  simp only [flagProjection, Matrix.trace_single_mul, one_smul]
  abel

lemma theta_cp (d : ℕ) {F G : Map (Fin d) (Fin d)} (hF : CP F) (hG : CP G) :
    CP (theta d F G) := by
  rw [theta_decomposition]
  apply cp_add
  · apply cp_add
    · apply cp_add
      · exact cp_add
          (cp_smul (cp_comp (cp_ad _) (cp_comp hG (cp_ad _))) (coefficient_pos hG).le)
          (cp_smul (cp_comp (cp_ad _) (cp_comp hF (cp_ad _))) (coefficient_pos hF).le)
      · exact cp_comp (cp_measureFlag _ (defect_psd hF)) (cp_ad _)
    · exact cp_comp (cp_measureFlag _ (defect_psd hG)) (cp_ad _)
  · exact cp_measureFlag _ (flag_psd d)

lemma theta_transpose_decomposition (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    transposeMap.comp (theta d F G) =
      (coefficient G : ℂ) • ((ad (W0 d)).comp ((transposeMap.comp G).comp (ad (W1 d)ᴴ))) +
      (coefficient F : ℂ) • ((ad (W1 d)).comp ((transposeMap.comp F).comp (ad (W0 d)ᴴ))) +
      (measureFlag d (defect F)).comp (ad (W0 d)ᴴ) +
      (measureFlag d (defect G)).comp (ad (W1 d)ᴴ) +
      measureFlag d (flagProjection d) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, transposeMap_apply, theta,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_add, Matrix.transpose_smul,
    W0, W1, flag_transpose, LinearMap.add_apply, LinearMap.smul_apply,
    measureFlag, ad_apply, Matrix.conjTranspose_conjTranspose, add_smul]
  simp only [Matrix.transpose_mul, ← coord_transpose, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  simp only [flagProjection, Matrix.trace_single_mul, one_smul]
  abel

lemma theta_ppt (d : ℕ) {F G : Map (Fin d) (Fin d)} (hF : PPT F) (hG : PPT G) :
    PPT (theta d F G) := by
  refine ⟨theta_cp d hF.1 hG.1, ?_⟩
  rw [theta_transpose_decomposition]
  apply cp_add
  · apply cp_add
    · apply cp_add
      · exact cp_add
          (cp_smul (cp_comp (cp_ad _) (cp_comp hG.2 (cp_ad _))) (coefficient_pos hG.1).le)
          (cp_smul (cp_comp (cp_ad _) (cp_comp hF.2 (cp_ad _))) (coefficient_pos hF.1).le)
      · exact cp_comp (cp_measureFlag _ (defect_psd hF.1)) (cp_ad _)
    · exact cp_comp (cp_measureFlag _ (defect_psd hG.1)) (cp_ad _)
  · exact cp_measureFlag _ (flag_psd d)

variable {n m : Type} [Fintype n] [Fintype m]

lemma defect_trace [DecidableEq n] (F : Map n m) (B : Mat n) :
    Matrix.trace (defect F * B) = Matrix.trace B - (coefficient F : ℂ) * Matrix.trace (F B) := by
  simp [defect, Matrix.sub_mul, effect_trace]

lemma trace_ad_isometry [DecidableEq n] (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (B : Mat n) :
    Matrix.trace (ad V B) = Matrix.trace B := by
  rw [ad_apply, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

lemma trace_two_blocks (d : ℕ) (X : Mat (Space d)) :
    Matrix.trace X = Matrix.trace ((W0 d)ᴴ * X * W0 d) +
      Matrix.trace ((W1 d)ᴴ * X * W1 d) + X (flag d) (flag d) := by
  rw [W0, W1, coord_compress, coord_compress]
  simp [Matrix.trace, Matrix.diag, Space, first, second, flag, Fintype.sum_sum_type]

lemma theta_tracePreserving (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    TracePreserving (theta d F G) := by
  intro X
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.trace_add, Matrix.trace_smul]
  rw [trace_ad_isometry _ (W0_isometry d), trace_ad_isometry _ (W1_isometry d),
    defect_trace, defect_trace]
  have hflag : Matrix.trace (flagProjection d) = 1 := by
    simp [flagProjection, Matrix.trace, Matrix.diag, Matrix.single_apply, flag]
  rw [hflag]
  simp only [smul_eq_mul, mul_one]
  rw [trace_two_blocks d X]
  ring

end ChannelCompletion

end

end OAI
