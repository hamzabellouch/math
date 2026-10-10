import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def RowSqBound (C : α → E →L[ℂ] E) (k : ℝ) : Prop :=
  ∀ x : α → E, ‖∑ a, C a (x a)‖ ^ 2 ≤ k * ∑ a, ‖x a‖ ^ 2

def ColSqBound (C : α → E →L[ℂ] E) (k : ℝ) : Prop :=
  ∀ x : E, (∑ a, ‖C a x‖ ^ 2) ≤ k * ‖x‖ ^ 2

def MatrixSqBound (T : α → β → E →L[ℂ] E) (k : ℝ) : Prop :=
  ∀ x : β → E, (∑ a, ‖∑ b, T a b (x b)‖ ^ 2) ≤ k * ∑ b, ‖x b‖ ^ 2

theorem RowSqBound.norm_le {C : α → E →L[ℂ] E} {t : ℝ}
    (h : RowSqBound C (t^2)) (ht : 0 ≤ t) (a : α) : ‖C a‖ ≤ t := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ ht
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).mp
  have h' := h (Pi.single a x)
  simpa only [Pi.single_apply, apply_ite, map_zero, norm_zero,
    ite_pow, zero_pow two_ne_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_pow] using h'

theorem RowSqBound.star_col [CompleteSpace E] {C : α → E →L[ℂ] E} {k : ℝ}
    (h : RowSqBound C k)
    (hk : 0 ≤ k) : ColSqBound (fun a => star (C a)) k := by
  intro x
  let s : ℝ := ∑ a, ‖star (C a) x‖ ^ 2
  let y : E := ∑ a, C a (star (C a) x)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hi : ⟪y,x⟫_ℂ = (s : ℂ) := by
    dsimp only [y, s]
    simp only [sum_inner, Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change ⟪star (C a) x, star (C a) x⟫_ℂ = _
    simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
  have hineq : s ≤ ‖y‖ * ‖x‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) y x
    rw [hi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at hh
    exact hh
  have hy : ‖y‖ ^ 2 ≤ k * s := h (fun a => star (C a) x)
  have hsquare : s ^ 2 ≤ (‖y‖ * ‖x‖) ^ 2 :=
    (sq_le_sq₀ hs (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hineq
  have hmul := mul_le_mul_of_nonneg_right hy (sq_nonneg ‖x‖)
  change s ≤ k * ‖x‖ ^ 2
  by_cases hzero : s = 0
  · rw [hzero]; positivity
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    nlinarith [mul_pow ‖y‖ ‖x‖ 2]

theorem RowSqBound.reindex {C : α → E →L[ℂ] E} {k : ℝ} (h : RowSqBound C k)
    (e : β ≃ α) : RowSqBound (fun b => C (e b)) k := by
  intro x
  have hr := h (fun a => x (e.symm a))
  simpa only [← Equiv.sum_comp e, e.symm_apply_apply] using hr

theorem RowSqBound.prod {C : α → E →L[ℂ] E} {D : β → E →L[ℂ] E} {k l : ℝ}
    (hC : RowSqBound C k) (hD : RowSqBound D l) (hk : 0 ≤ k) :
    RowSqBound (fun p : α × β => C p.1 * D p.2) (k * l) := by
  intro x
  calc
    _ = ‖∑ a, C a (∑ b, D b (x (a,b)))‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, map_sum, mul_apply_eq_comp]
    _ ≤ k * ∑ a, ‖∑ b, D b (x (a,b))‖ ^ 2 := hC _
    _ ≤ k * ∑ a, l * ∑ b, ‖x (a,b)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hk
      exact Finset.sum_le_sum (fun a _ => hD _)
    _ = (k * l) * ∑ p, ‖x p‖ ^ 2 := by
      simp only [Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

theorem row_matrix_col {C : α → E →L[ℂ] E} {D : β → E →L[ℂ] E}
    {T : α → β → E →L[ℂ] E} {k m l : ℝ}
    (hC : RowSqBound C k) (hT : MatrixSqBound T m) (hD : ColSqBound D l)
    (hk : 0 ≤ k) (hm : 0 ≤ m) (x : E) :
    ‖∑ a, ∑ b, (C a * T a b * D b) x‖ ^ 2 ≤ (k * m * l) * ‖x‖ ^ 2 := by
  calc
    _ = ‖∑ a, C a (∑ b, T a b (D b x))‖ ^ 2 := by
      simp only [map_sum, mul_apply_eq_comp]
    _ ≤ k * ∑ a, ‖∑ b, T a b (D b x)‖ ^ 2 := hC _
    _ ≤ k * (m * ∑ b, ‖D b x‖ ^ 2) := mul_le_mul_of_nonneg_left (hT _) hk
    _ ≤ k * (m * (l * ‖x‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD x) hm) hk
    _ = _ := by ring

def tupleOp {n : ℕ} (C : Fin n → α → E →L[ℂ] E) (a : Fin n → α) : E →L[ℂ] E :=
  (List.ofFn (fun j => C j (a j))).prod

theorem tupleOp_row {n : ℕ} {C : Fin n → α → E →L[ℂ] E} {k : ℝ}
    (hk : 0 ≤ k) (hC : ∀ j, RowSqBound (C j) k) :
    RowSqBound (tupleOp C) (k ^ n) := by
  induction n with
  | zero =>
    intro x
    simp [tupleOp]
  | succ n ih =>
    have h := (hC 0).prod (ih (fun j => hC j.succ)) hk
    have hr := h.reindex (Fin.consEquiv (fun _ : Fin (n+1) => α)).symm
    rw [pow_succ']
    convert hr using 1
    funext a
    simp only [tupleOp, List.ofFn_succ, List.prod_cons, Fin.consEquiv_symm_apply]
    rfl

theorem ColSqBound.reindex {C : α → E →L[ℂ] E} {k : ℝ} (h : ColSqBound C k)
    (e : β ≃ α) : ColSqBound (fun b => C (e b)) k := by
  intro x
  calc
    _ = ∑ a, ‖C a x‖ ^ 2 := Equiv.sum_comp e _
    _ ≤ _ := h x

theorem ColSqBound.prod {C : α → E →L[ℂ] E} {D : β → E →L[ℂ] E} {k l : ℝ}
    (hC : ColSqBound C k) (hD : ColSqBound D l) (hk : 0 ≤ k) :
    ColSqBound (fun p : α × β => C p.1 * D p.2) (k * l) := by
  intro x
  calc
    _ = ∑ b, ∑ a, ‖C a (D b x)‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, mul_apply_eq_comp]
      exact Finset.sum_comm
    _ ≤ ∑ b, k * ‖D b x‖ ^ 2 := Finset.sum_le_sum (fun b _ => hC _)
    _ = k * ∑ b, ‖D b x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ k * (l * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left (hD x) hk
    _ = _ := by ring

theorem tupleOp_col {n : ℕ} {C : Fin n → α → E →L[ℂ] E} {k : ℝ}
    (hk : 0 ≤ k) (hC : ∀ j, ColSqBound (C j) k) :
    ColSqBound (tupleOp C) (k ^ n) := by
  induction n with
  | zero =>
    intro x
    simp [tupleOp]
  | succ n ih =>
    have h := (hC 0).prod (ih (fun j => hC j.succ)) hk
    have hr := h.reindex (Fin.consEquiv (fun _ : Fin (n+1) => α)).symm
    rw [pow_succ']
    convert hr using 1
    funext a
    simp only [tupleOp, List.ofFn_succ, List.prod_cons, Fin.consEquiv_symm_apply]
    rfl

theorem row_matrix_col_norm {C : α → E →L[ℂ] E} {D : β → E →L[ℂ] E}
    {T : α → β → E →L[ℂ] E} {k m l : ℝ}
    (hC : RowSqBound C (k ^ 2)) (hT : MatrixSqBound T (m ^ 2))
    (hD : ColSqBound D (l ^ 2)) (hk : 0 ≤ k) (hm : 0 ≤ m) (hl : 0 ≤ l) :
    ‖∑ a, ∑ b, C a * T a b * D b‖ ≤ k * m * l := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := row_matrix_col hC hT hD (sq_nonneg _) (sq_nonneg _) x
  simpa only [sum_apply, mul_pow, mul_assoc] using h

theorem matrixSqBound_iff {T : α → β → E →L[ℂ] E} {k : ℝ} (hk : 0 ≤ k) :
    MatrixSqBound T (k ^ 2) ↔
    ∀ x : β → E,
      ‖WithLp.toLp 2 (fun a => ∑ b, T a b (x b))‖ ≤ k * ‖WithLp.toLp 2 x‖ := by
  constructor
  · intro h x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))).mp
    simpa only [PiLp.norm_sq_eq_of_L2, mul_pow, WithLp.ofLp_toLp] using h x
  · intro h x
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))).mpr (h x)
    simpa only [PiLp.norm_sq_eq_of_L2, mul_pow, WithLp.ofLp_toLp] using hs

theorem MatrixSqBound.add {S T : α → β → E →L[ℂ] E} {k l : ℝ}
    (hS : MatrixSqBound S (k ^ 2)) (hT : MatrixSqBound T (l ^ 2))
    (hk : 0 ≤ k) (hl : 0 ≤ l) :
    MatrixSqBound (fun a b => S a b + T a b) ((k + l) ^ 2) := by
  apply (matrixSqBound_iff (add_nonneg hk hl)).mpr
  intro x
  have he : (fun a => ∑ b, (S a b + T a b) (x b)) =
      (fun a => ∑ b, S a b (x b)) + (fun a => ∑ b, T a b (x b)) := by
    funext a
    simp only [add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [he, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (by
    simpa only [add_mul] using add_le_add ((matrixSqBound_iff hk).mp hS x)
      ((matrixSqBound_iff hl).mp hT x))

omit [InnerProductSpace ℂ E] [Fintype α] in
theorem norm_sum_sq_le_card (s : Finset α) (x : α → E) :
    ‖∑ a ∈ s, x a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, ‖x a‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun a => ‖x a‖)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s x) 2
  exact hn.trans (by simpa using h)

theorem projection_sum_norm_sq [CompleteSpace E] (P : α → E →L[ℂ] E)
    (hP : ∀ a, IsStarProjection (P a))
    (horth : ∀ a b, a ≠ b → P a * P b = 0) (x : α → E) :
    ‖∑ a, P a (x a)‖ ^ 2 = ∑ a, ‖P a (x a)‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  have he a b (hab : a ≠ b) : ⟪P a (x a), P b (x b)⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change ⟪x a, star (P a) (P b (x b))⟫_ℂ = 0
    rw [(hP a).isSelfAdjoint.star_eq,
      ← mul_apply_eq_comp, horth a b hab, zero_apply, inner_zero_right]
  have hi : ⟪∑ a, P a (x a), ∑ a, P a (x a)⟫_ℂ =
      ∑ a, ⟪P a (x a), P a (x a)⟫_ℂ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_eq_single a (fun b _ hba => he b a hba) (by simp)
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_pow] using hi

variable [DecidableEq β]

theorem sum_incidence (s : α → Finset β) (f : β → ℝ) :
    (∑ a, ∑ b ∈ s a, f b) =
      ∑ b, ((Finset.univ.filter (fun a => b ∈ s a)).card : ℝ) * f b := by
  classical
  calc
    _ = ∑ a, ∑ b, if b ∈ s a then f b else 0 := by simp
    _ = ∑ b, ∑ a, if b ∈ s a then f b else 0 := Finset.sum_comm
    _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem projection_incidence_bound [CompleteSpace E]
    (P : γ → E →L[ℂ] E) (hP : ∀ c, IsStarProjection (P c))
    (horth : ∀ c e, c ≠ e → P c * P e = 0) (hsum : ∑ c, P c = 1)
    (s : α → γ → Finset β) (R C : ℕ)
    (hrow : ∀ a c, (s a c).card ≤ R)
    (hcol : ∀ b c, (Finset.univ.filter (fun a => b ∈ s a c)).card ≤ C) :
    MatrixSqBound (fun a b => ∑ c, if b ∈ s a c then P c else 0)
      ((R : ℝ) * C) := by
  classical
  intro x
  have he a : (∑ b, (∑ c, if b ∈ s a c then P c else 0) (x b)) =
      ∑ c, P c (∑ b ∈ s a c, x b) := by
    simp only [sum_apply, map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    have hi b : (if b ∈ s a c then P c else (0 : E →L[ℂ] E)) (x b) =
        if b ∈ s a c then P c (x b) else 0 := by split_ifs <;> rfl
    simp only [hi]
    simp
  simp only [he, projection_sum_norm_sq P hP horth]
  have hind c : (∑ a, ∑ b ∈ s a c, ‖P c (x b)‖ ^ 2) ≤
      (C : ℝ) * ∑ b, ‖P c (x b)‖ ^ 2 := by
    rw [sum_incidence, Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcol b c) (sq_nonneg _))
  have hnorm b : (∑ c, ‖P c (x b)‖ ^ 2) = ‖x b‖ ^ 2 := by
    rw [← projection_sum_norm_sq P hP horth, ← sum_apply, hsum]
    rfl
  calc
    _ ≤ ∑ a, ∑ c, (R : ℝ) * ∑ b ∈ s a c, ‖P c (x b)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      rw [map_sum]
      exact (norm_sum_sq_le_card _ _).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hrow a c)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = (R : ℝ) * ∑ c, ∑ a, ∑ b ∈ s a c, ‖P c (x b)‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ (R : ℝ) * ∑ c, (C : ℝ) * ∑ b, ‖P c (x b)‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hind c))
        (Nat.cast_nonneg _)
    _ = ((R : ℝ) * C) * ∑ b, ‖x b‖ ^ 2 := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm, show (∑ b, ∑ c, ‖P c (x b)‖ ^ 2) =
        ∑ b, ‖x b‖ ^ 2 from Finset.sum_congr rfl (fun b _ => hnorm b)]
      ring

omit [DecidableEq β]

theorem scalar_matrix_bound (w : α → β → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (R C : ℝ) (hR : 0 ≤ R) (_hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, w a b ≤ R) (hcol : ∀ b, ∑ a, w a b ≤ C) :
    MatrixSqBound (fun a b => (w a b : ℂ) • (1 : E →L[ℂ] E)) (R * C) := by
  intro x
  have hs a : ‖∑ b, ((w a b : ℂ) • (1 : E →L[ℂ] E)) (x b)‖ ^ 2 ≤
      R * ∑ b, w a b * ‖x b‖ ^ 2 := by
    have hn : ‖∑ b, ((w a b : ℂ) • (1 : E →L[ℂ] E)) (x b)‖ ≤
        ∑ b, w a b * ‖x b‖ := by
      simpa only [smul_apply, one_apply_eq_self, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw _ _)] using
        norm_sum_le Finset.univ (fun b => ((w a b : ℂ) • (1 : E →L[ℂ] E)) (x b))
    have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (f := fun b => w a b) (g := fun b => w a b * ‖x b‖ ^ 2)
      (r := fun b => w a b * ‖x b‖)
      (fun b _ => hw a b) (fun b _ => mul_nonneg (hw a b) (sq_nonneg _))
      (fun b _ => by nlinarith)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hh.trans
      (mul_le_mul_of_nonneg_right (hrow a)
        (Finset.sum_nonneg (fun b _ => mul_nonneg (hw _ _) (sq_nonneg _)))))
  calc
    _ ≤ ∑ a, R * ∑ b, w a b * ‖x b‖ ^ 2 := Finset.sum_le_sum (fun a _ => hs a)
    _ = R * ∑ b, (∑ a, w a b) * ‖x b‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ b, C * ‖x b‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_right (hcol b) (sq_nonneg _))) hR
    _ = (R * C) * ∑ b, ‖x b‖ ^ 2 := by simp only [← Finset.mul_sum, mul_assoc]

theorem MatrixSqBound.compress {T : α → β → E →L[ℂ] E} {k : ℝ}
    (hT : MatrixSqBound T k) (hk : 0 ≤ k) (Q : E →L[ℂ] E) (hQ : ‖Q‖ ≤ 1) :
    MatrixSqBound (fun a b => Q * T a b * Q) k := by
  have hn (x : E) : ‖Q x‖ ≤ ‖x‖ :=
    (Q.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  intro x
  calc
    _ = ∑ a, ‖Q (∑ b, T a b (Q (x b)))‖ ^ 2 := by
      simp only [mul_apply_eq_comp, map_sum]
    _ ≤ ∑ a, ‖∑ b, T a b (Q (x b))‖ ^ 2 := by
      exact Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hn _) 2)
    _ ≤ k * ∑ b, ‖Q (x b)‖ ^ 2 := hT _
    _ ≤ k * ∑ b, ‖x b‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun b _ => pow_le_pow_left₀ (norm_nonneg _) (hn _) 2)) hk

theorem MatrixSqBound.smul {T : α → β → E →L[ℂ] E} {k : ℝ}
    (hT : MatrixSqBound T k) (c : ℂ) :
    MatrixSqBound (fun a b => c • T a b) (‖c‖ ^ 2 * k) := by
  intro x
  calc
    _ = ‖c‖ ^ 2 * ∑ a, ‖∑ b, T a b (x b)‖ ^ 2 := by
      simp only [smul_apply, ← Finset.smul_sum, norm_smul, mul_pow, Finset.mul_sum]
    _ ≤ ‖c‖ ^ 2 * (k * ∑ b, ‖x b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hT x) (sq_nonneg _)
    _ = _ := by ring

end

end KKFreeWords
end

end OAI
