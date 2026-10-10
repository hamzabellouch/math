import Mathlib

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev M (ι : Type*) := Matrix ι ι ℂ

lemma entry_norm_le (A : M ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ ι := PiLp.single 2 j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hi := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A e) i
  have hval : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A e).ofLp i = A i j := by
    simp only [Matrix.ofLp_toEuclideanCLM, e, PiLp.ofLp_single, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  rw [hval] at hi
  exact hi.trans (by simpa only [he, mul_one, ← Matrix.cstar_norm_def] using ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A).le_opNorm e)

lemma trace_norm_le (A : M ι) : ‖Matrix.trace A‖ ≤ Fintype.card ι * ‖A‖ := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ := Finset.sum_le_sum fun i _ => entry_norm_le A i i
    _ = _ := by simp

lemma prod_norm_le_one (l : List (M ι))
    (hl : ∀ a ∈ l, ‖a‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil =>
      change ‖(1 : M ι)‖ ≤ 1
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  | cons a l ih =>
      rw [List.prod_cons]
      exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hl _ (by simp))).trans
          (ih (fun b hb => hl b (by simp [hb]))))

def diagPower (d : ι → ℝ) (z : ℂ) : M ι :=
  Matrix.diagonal fun i => if d i = 0 then 0 else Complex.exp (z * (Real.log (d i) : ℂ))

lemma diagPower_add (d : ι → ℝ) (z w : ℂ) :
    diagPower d (z+w) = diagPower d z * diagPower d w := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagPower, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [add_mul, Complex.exp_add]
  · simp [diagPower, Matrix.diagonal_apply_ne _ hij]

lemma diagPower_norm_le_one (d : ι → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd : ∀ i, d i ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖diagPower d z‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs with hi
  · simp
  · rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hz (Real.log_nonpos (hd0 i) (hd i))

lemma diagPower_imag_norm_le_one (d : ι → ℝ) (t : ℝ) :
    ‖diagPower d ((t : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> simp [Complex.norm_exp, Complex.mul_re]

omit [Fintype ι] in
lemma diagPower_one (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    diagPower d 1 = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagPower, Matrix.diagonal_apply_eq, one_mul]
    by_cases hi : d i = 0
    · simp [hi]
    · rw [ite_eq_right hi, ← Complex.ofReal_exp, Real.exp_log (lt_of_le_of_ne (hd i) (Ne.symm hi))]
  · simp [diagPower, Matrix.diagonal_apply_ne _ hij]

lemma differentiable_diagPower (d : ι → ℝ) : Differentiable ℂ (diagPower d) := by
  let L := (Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap
  change Differentiable ℂ (fun z => L (fun i => if d i = 0 then 0 else
    Complex.exp (z * (Real.log (d i) : ℂ))))
  apply L.differentiable.comp
  apply differentiable_pi.mpr
  intro i
  by_cases hi : d i = 0
  · simp [hi]
  · simp only [hi, ite_false]
    exact Complex.differentiable_exp.comp (differentiable_id.mul_const _)

def word {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ) (x : Fin m → ℂ) : M ι :=
  (List.ofFn (fun j => A j * diagPower (d j) (x j))).prod

def traceWord {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ) (x : Fin m → ℂ) : ℂ :=
  Matrix.trace (word A d x)

lemma word_norm_le_one {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ) (hA : ∀ j, ‖A j‖ ≤ 1) (hd0 : ∀ j i, 0 ≤ d j i) (hd : ∀ j i, d j i ≤ 1)
    (hx : ∀ j, 0 ≤ (x j).re) : ‖word A d x‖ ≤ 1 := by
  apply prod_norm_le_one
  intro B hB
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hB
  exact (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hA j)).trans
      (diagPower_norm_le_one (d j) (hd0 j) (hd j) (hx j)))

lemma differentiable_word {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ → ℂ) (hx : ∀ j, Differentiable ℂ (x j)) :
    Differentiable ℂ (fun z => word A d (fun j => x j z)) := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
      simp only [word, List.ofFn_succ, List.prod_cons]
      apply Differentiable.mul
      · have h₀ : Differentiable ℂ (fun z => diagPower (d 0) (x 0 z)) :=
          (differentiable_diagPower (d 0)).comp (hx 0)
        exact (differentiable_const (A 0)).mul h₀
      · exact ih (fun j => A j.succ) (fun j => d j.succ) (fun j => x j.succ)
          (fun j => hx j.succ)

lemma differentiable_traceWord {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ → ℂ) (hx : ∀ j, Differentiable ℂ (x j)) :
    Differentiable ℂ (fun z => traceWord A d (fun j => x j z)) := by
  exact (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.differentiable.comp
    (differentiable_word A d x hx)

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagReal (s : ι → ℝ) : M ι := Matrix.diagonal (fun i => (s i : ℂ))

omit [Fintype ι] in
lemma star_diagReal (s : ι → ℝ) : star (diagReal s) = diagReal s := by
  simp [diagReal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

lemma diagReal_mul (s t : ι → ℝ) : diagReal s * diagReal t = diagReal (fun i => s i*t i) := by
  simp [diagReal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

omit [DecidableEq ι] in
lemma gram_product (X Y : M ι) :
    star (X*Y) * (X*Y) = star Y * (star X * X) * Y := by
  simp only [star_mul, mul_assoc]

lemma gram_diagonal_factor (X : M ι) (s : ι → ℝ)
    (hX : star X * X = diagReal (fun i => s i ^ 2)) :
    ∃ U : M ι, ‖U‖ ≤ 1 ∧ X = U * diagReal s := by
  let t : ι → ℝ := fun i => (s i)⁻¹
  let U := X * diagReal t
  have hU : star U * U = diagReal (fun i => if s i = 0 then 0 else 1) := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    congr 1
    funext i
    dsimp [t]
    split_ifs with hi
    · simp [hi]
    · field_simp
  have hUnorm : ‖U‖ ≤ 1 := by
    have h : ‖star U * U‖ ≤ 1 := by
      rw [hU, diagReal, Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      split_ifs <;> norm_num
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg U]
  let w : ι → ℝ := fun i => 1 - t i * s i
  have hz : star (X * diagReal w) * (X * diagReal w) = 0 := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    have hw : (fun i => (w i * s i ^ 2) * w i) = 0 := by
      funext i
      dsimp [w, t]
      by_cases hi : s i = 0 <;> simp [hi]
    rw [hw]
    simp [diagReal]
  have hzero : X * diagReal w = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  have hw : diagReal w = 1 - diagReal t * diagReal s := by
    rw [diagReal_mul]
    dsimp [diagReal, w]
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  rw [hw, mul_sub, mul_one] at hzero
  refine ⟨U, hUnorm, ?_⟩
  exact (sub_eq_zero.mp hzero).trans (mul_assoc _ _ _).symm

theorem exists_partial_svd (A : M ι) :
    ∃ (U : M ι) (V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ ‖U‖ ≤ 1 ∧
      A = U * diagReal s * star (V : M ι) ∧
      star A * A = (V : M ι) * diagReal (fun i => s i ^ 2) * star (V : M ι) := by
  let h := Matrix.isHermitian_conjTranspose_mul_self A
  let V := h.eigenvectorUnitary
  let s : ι → ℝ := fun i => Real.sqrt (h.eigenvalues i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hs : ∀ i, s i ^ 2 = h.eigenvalues i := fun i =>
    Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  have hdiag : star (V : M ι) * (star A * A) * (V : M ι) =
      diagReal (fun i => s i ^ 2) := by
    simpa only [V, s, hs, diagReal, Matrix.star_eq_conjTranspose, Function.comp_def,
      Unitary.conjStarAlgAut_star_apply] using! h.conjStarAlgAut_star_eigenvectorUnitary
  have hgram : star (A * (V : M ι)) * (A * (V : M ι)) =
      diagReal (fun i => s i ^ 2) := by rw [gram_product, hdiag]
  obtain ⟨U, hU, heq⟩ := gram_diagonal_factor (A * (V : M ι)) s hgram
  have hVV : (V : M ι) * star (V : M ι) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
  refine ⟨U, V, s, hs0, hU, ?_, ?_⟩
  · have heq' := congrArg (fun X => X * star (V : M ι)) heq
    simpa only [mul_assoc, hVV, mul_one] using heq'
  · calc
      star A * A = ((V : M ι) * star (V : M ι)) * (star A * A) *
          ((V : M ι) * star (V : M ι)) := by rw [hVV, one_mul, mul_one]
      _ = (V : M ι) * (star (V : M ι) * (star A * A) * (V : M ι)) *
          star (V : M ι) := by simp only [mul_assoc]
      _ = _ := by rw [hdiag]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
