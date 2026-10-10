import OAI.Probability.SwitchChain.SpectralFromSquare

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace
open WithLp

namespace Problem315.Analytic

variable {α : Type*} [Fintype α]

def zeroSumSpace (α : Type*) [Fintype α] : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∑ i, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, x i = 0 at hx
    change ∑ i, y i = 0 at hy
    change ∑ i, (x + y) i = 0
    simp only [PiLp.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ i, x i = 0 at hx
    change ∑ i, (c • x) i = 0
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

@[simp] theorem mem_zeroSumSpace (f : EuclideanSpace ℝ α) :
    f ∈ zeroSumSpace α ↔ ∑ i, f i = 0 := Iff.rfl

lemma euclidean_inner_eq_sum (f g : EuclideanSpace ℝ α) :
    ⟪f, g⟫ = ∑ i, f i * g i := by
  simp [PiLp.inner_apply, mul_comm]

lemma euclidean_norm_sq_eq_sum (f : EuclideanSpace ℝ α) :
    ‖f‖ ^ 2 = ∑ i, (f i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, euclidean_inner_eq_sum]
  simp [pow_two]

variable [DecidableEq α]

lemma matrix_preserves_zeroSum (K : Matrix α α ℝ)
    (hcols : ∀ j, ∑ i, K i j = 1) (f : EuclideanSpace ℝ α)
    (hf : f ∈ zeroSumSpace α) : Matrix.toEuclideanLin K f ∈ zeroSumSpace α := by
  change ∑ i, (Matrix.toEuclideanLin K f) i = 0
  simp only [Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcols, one_mul]
  exact hf

theorem matrix_centered_norm_decay (K : Matrix α α ℝ)
    (hsymm : K.IsSymm) (hcols : ∀ j, ∑ i, K i j = 1)
    {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
    (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
      γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
    (t : ℕ) (f : EuclideanSpace ℝ α) (hf : ∑ i, f i = 0) :
    ‖(Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t] f‖ ≤
      Real.exp (-γ * (t : ℝ)) * ‖f‖ := by
  let T := Matrix.toEuclideanLin K
  have hinv := matrix_preserves_zeroSum K hcols
  let S := T.restrict hinv
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr hsymm)
  have hS : S.IsSymmetric := hT.restrict_invariant hinv
  have hSpos : ∀ x : zeroSumSpace α, 0 ≤ ⟪x, S x⟫ := by
    intro x
    change 0 ≤ ⟪(x : EuclideanSpace ℝ α), T x⟫
    simpa only [T, euclidean_inner_eq_sum, Matrix.toLpLin_apply, ofLp_toLp,
      Matrix.mulVec, dotProduct] using hpos (fun i => x.val i)
  have hSgap : ∀ x : zeroSumSpace α, ⟪x, S x⟫ ≤ (1 - γ) * ‖x‖ ^ 2 := by
    intro x
    change ⟪(x : EuclideanSpace ℝ α), T x⟫ ≤ (1 - γ) * ‖(x : EuclideanSpace ℝ α)‖ ^ 2
    rw [euclidean_inner_eq_sum, euclidean_norm_sq_eq_sum]
    simp only [T, Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct]
    have hh := hgap (fun i => x.val i) x.property
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← pow_two] at hh
    linarith
  have hdec := norm_iterate_le_exp_of_inner_bounds S hS hγ hSpos hSgap t ⟨f, hf⟩
  have hiter (k : ℕ) :
      ((S : zeroSumSpace α → zeroSumSpace α)^[k] ⟨f, hf⟩).val =
        (T : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[k] f := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [Function.iterate_succ_apply']
        change T (((S : zeroSumSpace α → zeroSumSpace α)^[k] ⟨f, hf⟩).val) = _
        rw [ih]
  change ‖(((S : zeroSumSpace α → zeroSumSpace α)^[t] ⟨f, hf⟩).val)‖ ≤
    Real.exp (-γ * (t : ℝ)) * ‖f‖ at hdec
  rwa [hiter] at hdec

omit [DecidableEq α] in
lemma sum_abs_le_sqrt_card_mul_norm (f : EuclideanSpace ℝ α) :
    (∑ i, |f i|) ≤ Real.sqrt (Fintype.card α : ℝ) * ‖f‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : α => (1 : ℝ)) (fun i => |f i|)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs, ← euclidean_norm_sq_eq_sum, Real.sqrt_sq (norm_nonneg f)] using h

def centeredPoint (a : α) : EuclideanSpace ℝ α :=
  toLp 2 (fun i => (if i = a then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ))

lemma centeredPoint_sum (a : α) : ∑ i, centeredPoint a i = 0 := by
  have : Nonempty α := ⟨a⟩
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centeredPoint, Finset.sum_sub_distrib, hn]

lemma centeredPoint_norm_sq (a : α) :
    ‖centeredPoint a‖ ^ 2 = 1 - 1 / (Fintype.card α : ℝ) := by
  have : Nonempty α := ⟨a⟩
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [euclidean_norm_sq_eq_sum]
  simp only [centeredPoint, ofLp_toLp, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [ite_pow, one_pow, zero_pow (by omega : (2 : ℕ) ≠ 0), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

lemma centeredPoint_norm_le_one (a : α) : ‖centeredPoint a‖ ≤ 1 := by
  have h := centeredPoint_norm_sq a
  have hn : 0 ≤ 1 / (Fintype.card α : ℝ) := by positivity
  nlinarith [norm_nonneg (centeredPoint a)]

lemma matrix_pow_row_sum (K : Matrix α α ℝ)
    (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) : ∀ i, ∑ j, (K ^ t) i j = 1 := by
  induction t with
  | zero => intro i; simp [Matrix.one_apply]
  | succ t ih =>
      intro i
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrows, mul_one]
      exact ih i

lemma matrix_iterate_centeredPoint (K : Matrix α α ℝ)
    (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) (a i : α) :
    ((Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t]
      (centeredPoint a)) i = (K ^ t) i a - 1 / (Fintype.card α : ℝ) := by
  rw [← Module.End.pow_apply]
  change ((Matrix.toLpLin 2 2 K ^ t) (centeredPoint a)) i = _
  rw [← Matrix.toLpLin_pow, Matrix.toLpLin_apply]
  simp only [ofLp_toLp, Matrix.mulVec, dotProduct, centeredPoint, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, matrix_pow_row_sum K hrows t,
    one_mul]
  simp

theorem matrix_tv_bound_of_gap (K : Matrix α α ℝ)
    (hsymm : K.IsSymm) (hrows : ∀ i, ∑ j, K i j = 1)
    {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
    (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
      γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
    (t : ℕ) (a : α) :
    (1 / 2 : ℝ) * (∑ i, |(K ^ t) a i - 1 / (Fintype.card α : ℝ)|) ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.exp (-γ * (t : ℝ)) := by
  have hcols : ∀ j, ∑ i, K i j = 1 := by
    intro j
    calc
      ∑ i, K i j = ∑ i, K j i := Finset.sum_congr rfl (fun i _ => hsymm.apply j i)
      _ = 1 := hrows j
  let f := (Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t]
    (centeredPoint a)
  have heq (i : α) : f i = (K ^ t) a i - 1 / (Fintype.card α : ℝ) := by
    dsimp only [f]
    rw [matrix_iterate_centeredPoint K hrows, (hsymm.pow t).apply a i]
  have hnorm : ‖f‖ ≤ Real.exp (-γ * (t : ℝ)) := by
    calc
      ‖f‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖centeredPoint a‖ :=
        matrix_centered_norm_decay K hsymm hcols hγ hpos hgap t
          (centeredPoint a) (centeredPoint_sum a)
      _ ≤ Real.exp (-γ * (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (centeredPoint_norm_le_one a) (Real.exp_nonneg _)
      _ = _ := mul_one _
  calc
    (1 / 2 : ℝ) * (∑ i, |(K ^ t) a i - 1 / (Fintype.card α : ℝ)|) =
        (1 / 2 : ℝ) * ∑ i, |f i| := by simp_rw [heq]
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (Fintype.card α : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_mul_norm f) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (Fintype.card α : ℝ) *
        Real.exp (-γ * (t : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = _ := by ring

end Problem315.Analytic

end

end OAI
