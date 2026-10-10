import OAI.Analysis.MutuallyUnbiased.Completion.Kraus

namespace OAI

/-!
# Realignment of a self-adjoint projection

The complement operator in Weiner's argument is an orthogonal projection whose
matrix is invariant under realignment. Its columns therefore form a finite
Kraus family; choosing an orthonormal basis of its range is unnecessary.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a matrix on pairs of indices to an ordinary matrix. -/
def applySuper (C : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ p, C (i, j) p * X p.1 p.2

omit [DecidableEq n] in
lemma applySuper_add (C : Matrix (n × n) (n × n) ℂ) (X Y : Matrix n n ℂ) :
    applySuper C (X + Y) = applySuper C X + applySuper C Y := by
  ext i j
  simp [applySuper, mul_add, Finset.sum_add_distrib]

omit [DecidableEq n] in
lemma applySuper_sub (C : Matrix (n × n) (n × n) ℂ) (X Y : Matrix n n ℂ) :
    applySuper C (X - Y) = applySuper C X - applySuper C Y := by
  ext i j
  simp [applySuper, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq n] in
lemma applySuper_smul (C : Matrix (n × n) (n × n) ℂ) (a : ℂ) (X : Matrix n n ℂ) :
    applySuper C (a • X) = a • applySuper C X := by
  ext i j
  simp [applySuper, Finset.mul_sum, mul_left_comm]

omit [DecidableEq n] in
lemma applySuper_real_smul (C : Matrix (n × n) (n × n) ℂ) (a : ℝ) (X : Matrix n n ℂ) :
    applySuper C (a • X) = a • applySuper C X := by
  simpa only [← Complex.coe_smul] using applySuper_smul C (a : ℂ) X

lemma applySuper_one (X : Matrix n n ℂ) : applySuper 1 X = X := by
  ext i j
  simp [applySuper, Matrix.one_apply]

omit [DecidableEq n] in
lemma applySuper_add_left (C D : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) :
    applySuper (C + D) X = applySuper C X + applySuper D X := by
  ext i j
  simp [applySuper, add_mul, Finset.sum_add_distrib]

omit [DecidableEq n] in
lemma applySuper_sub_left (C D : Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) :
    applySuper (C - D) X = applySuper C X - applySuper D X := by
  ext i j
  simp [applySuper, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
lemma applySuper_sum_left {κ : Type*} [Fintype κ]
    (C : κ → Matrix (n × n) (n × n) ℂ) (X : Matrix n n ℂ) :
    applySuper (∑ r, C r) X = ∑ r, applySuper (C r) X := by
  ext i j
  simp only [applySuper, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A column of a superoperator, reshaped as an ordinary matrix. -/
def superColumn (C : Matrix (n × n) (n × n) ℂ) (p : n × n) : Matrix n n ℂ :=
  fun i j => C (i, j) p

/-- The realignment symmetry relevant to a Kraus decomposition. -/
def IsRealigned (C : Matrix (n × n) (n × n) ℂ) : Prop :=
  ∀ i j k l, C (i, j) (k, l) = C (l, j) (k, i)

omit [DecidableEq n] in
lemma superColumn_fixed (C : Matrix (n × n) (n × n) ℂ) (hC : C * C = C)
    (p : n × n) : applySuper C (superColumn C p) = superColumn C p := by
  ext i j
  exact congrArg (fun A : Matrix (n × n) (n × n) ℂ => A (i, j) p) hC

lemma applySuper_one_entry (C : Matrix (n × n) (n × n) ℂ) (i j : n) :
    applySuper C 1 i j = ∑ k, C (i, j) (k, k) := by
  simp [applySuper, Fintype.sum_prod_type, Matrix.one_apply]

/-- A self-adjoint unital superoperator preserves the ordinary matrix trace. -/
theorem applySuper_trace (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hunital : applySuper C 1 = 1) (X : Matrix n n ℂ) :
    (applySuper C X).trace = X.trace := by
  have hentry (u v : n × n) : C u v = star (C v u) := by
    exact (congrArg (fun A : Matrix (n × n) (n × n) ℂ => A u v) hherm).symm
  have hdiag (i j : n) : (∑ k, C (k, k) (i, j)) = if i = j then 1 else 0 := by
    calc
      _ = star (∑ k, C (i, j) (k, k)) := by
        rw [star_sum]
        exact Finset.sum_congr rfl (fun k _ => hentry (k, k) (i, j))
      _ = star (applySuper C 1 i j) := by rw [applySuper_one_entry]
      _ = _ := by rw [hunital]; simp [Matrix.one_apply]
  calc
    (applySuper C X).trace = ∑ i, ∑ p, C (i, i) p * X p.1 p.2 := rfl
    _ = ∑ p, (∑ i, C (i, i) p) * X p.1 p.2 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = X.trace := by simp [hdiag, Fintype.sum_prod_type, Matrix.trace]

omit [DecidableEq n] in
/-- A Hermitian idempotent invariant under realignment is a Kraus sum of its
reshaped columns. -/
theorem applySuper_eq_kraus_columns (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (X : Matrix n n ℂ) : applySuper C X = kraus (superColumn C) X := by
  have hgram (u v : n × n) : ∑ a, star (C v a) * C u a = C u v := by
    have h := congrArg (fun A : Matrix (n × n) (n × n) ℂ => A u v)
      (show C * Cᴴ = C by rw [hherm, hidem])
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h
  have hmul (a b c : ℂ) : a * b * c = b * (a * c) := by ring
  ext i j
  symm
  calc
    kraus (superColumn C) X i j =
        ∑ l, ∑ k, X k l * (∑ a, star (C (k, i) a) * C (l, j) a) := by
      simp only [kraus, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, superColumn]
      simp_rw [Finset.sum_mul, hmul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ l, ∑ k, C (i, j) (k, l) * X k l := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      rw [hgram, ← hreal i j k l, mul_comm]
    _ = applySuper C X i j := by
      rw [Finset.sum_comm]
      simp only [applySuper, Fintype.sum_prod_type]

omit [DecidableEq n] in
lemma applySuper_conjTranspose (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (X : Matrix n n ℂ) : applySuper C Xᴴ = (applySuper C X)ᴴ := by
  simp only [applySuper_eq_kraus_columns C hherm hidem hreal, kraus_conjTranspose]

omit [DecidableEq n] in
lemma applySuper_eq_sum_smul_columns (C : Matrix (n × n) (n × n) ℂ)
    (X : Matrix n n ℂ) : applySuper C X = ∑ p, X p.1 p.2 • superColumn C p := by
  ext i j
  simp only [applySuper, Matrix.sum_apply, Matrix.smul_apply, superColumn, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Every fixed point of a unital realigned orthogonal projection commutes with
every reshaped column of that projection. -/
theorem commute_of_super_fixed (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1)
    (X : Matrix n n ℂ) (hX : applySuper C X = X) (p : n × n) :
    Commute X (superColumn C p) := by
  have hleft : ∑ q, (superColumn C q)ᴴ * superColumn C q = 1 := by
    simpa only [applySuper_eq_kraus_columns C hherm hidem hreal, kraus, Matrix.mul_one]
      using hunital
  have hright : ∑ q, superColumn C q * (superColumn C q)ᴴ = 1 := by
    apply right_unital_of_trace_preserving
    intro Y
    rw [← applySuper_eq_kraus_columns C hherm hidem hreal]
    exact applySuper_trace C hherm hunital Y
  apply commute_of_kraus_fixed (superColumn C) hleft hright X _ p
  rwa [← applySuper_eq_kraus_columns C hherm hidem hreal]

/-- The entire fixed space is commutative. Its elements are linear combinations
of the reshaped columns, which all commute with every fixed point. -/
theorem super_fixedPoints_commute (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1) (X Y : Matrix n n ℂ)
    (hX : applySuper C X = X) (hY : applySuper C Y = Y) : Commute X Y := by
  rw [← hY, applySuper_eq_sum_smul_columns]
  apply Commute.sum_right
  intro p _
  exact (commute_of_super_fixed C hherm hidem hreal hunital X hX p).smul_right _

/-- In particular the reshaped columns all commute. -/
theorem superColumns_commute (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hidem : C * C = C) (hreal : IsRealigned C)
    (hunital : applySuper C 1 = 1) (p q : n × n) :
    Commute (superColumn C p) (superColumn C q) :=
  commute_of_super_fixed C hherm hidem hreal hunital (superColumn C p)
    (superColumn_fixed C hidem p) q

/-- A Hermitian idempotent with zero trace is zero. -/
theorem hermitian_idempotent_eq_zero_of_trace_zero {I : Type*} [Fintype I]
    (C : Matrix I I ℂ) (hherm : Cᴴ = C) (hidem : C * C = C)
    (htrace : C.trace = 0) : C = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rwa [hherm, hidem]

end MUB6.Weiner

end OAI
