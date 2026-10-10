import OAI.Analysis.MutuallyUnbiased.Completion.Superoperator

namespace OAI

/-!
# The concrete complement supermatrix

The Hermitian and realignment symmetries are algebraic identities for arbitrary
complex vectors. Orthonormality and mutual unbiasedness are needed for the
separate unitality and idempotence identities.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]

/-- Supermatrix of the unnormalized trace map `X ↦ trace(X) I`. -/
def traceMatrix : Matrix (n × n) (n × n) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

/-- Supermatrix of the sum of rank-one pinching maps for a vector family. -/
def pinchingMatrix (v : κ → n → ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun p q => ∑ a, v a p.1 * star (v a p.2) * star (v a q.1) * v a q.2

/-- Candidate missing-basis projection for six bases in dimension six. -/
def complementMatrix (v : ι → κ → n → ℂ) : Matrix (n × n) (n × n) ℂ :=
  1 + traceMatrix - ∑ r, pinchingMatrix (v r)

omit [Fintype n] in
lemma traceMatrix_hermitian : (traceMatrix : Matrix (n × n) (n × n) ℂ)ᴴ = traceMatrix := by
  ext p q
  simp [traceMatrix, Matrix.conjTranspose_apply, and_comm]

omit [Fintype n] [DecidableEq n] in
lemma pinchingMatrix_hermitian (v : κ → n → ℂ) : (pinchingMatrix v)ᴴ = pinchingMatrix v := by
  ext p q
  simp only [Matrix.conjTranspose_apply, pinchingMatrix, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype n] in
lemma complementMatrix_hermitian (v : ι → κ → n → ℂ) :
    (complementMatrix v)ᴴ = complementMatrix v := by
  simp [complementMatrix, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_sum, traceMatrix_hermitian, pinchingMatrix_hermitian]

omit [Fintype n] [DecidableEq n] in
lemma pinchingMatrix_realigned (v : κ → n → ℂ) : IsRealigned (pinchingMatrix v) := by
  intro i j k l
  apply Finset.sum_congr rfl
  intro a _
  dsimp [pinchingMatrix]
  ring

omit [Fintype n] in
/-- The identity and trace supermatrices interchange under realignment. -/
lemma one_trace_realignment (i j k l : n) :
    (1 : Matrix (n × n) (n × n) ℂ) (i, j) (k, l) = traceMatrix (l, j) (k, i) := by
  simp [Matrix.one_apply, traceMatrix, Prod.mk.injEq, and_comm, eq_comm]

omit [Fintype n] in
lemma complementMatrix_realigned (v : ι → κ → n → ℂ) : IsRealigned (complementMatrix v) := by
  intro i j k l
  have hsum : (∑ r, pinchingMatrix (v r) (i, j) (k, l)) =
      ∑ r, pinchingMatrix (v r) (l, j) (k, i) := by
    apply Finset.sum_congr rfl
    intro r _
    exact pinchingMatrix_realigned (v r) i j k l
  have h₂ : traceMatrix (i, j) (k, l) = (1 : Matrix (n × n) (n × n) ℂ) (l, j) (k, i) :=
    (one_trace_realignment l j k i).symm
  simp only [complementMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply]
  rw [hsum, one_trace_realignment i j k l, h₂]
  ring

lemma applySuper_traceMatrix (X : Matrix n n ℂ) :
    applySuper traceMatrix X = X.trace • (1 : Matrix n n ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [applySuper, traceMatrix, Fintype.sum_prod_type, Matrix.trace]
  · simp [applySuper, traceMatrix, hij]

lemma traceMatrix_trace : (traceMatrix : Matrix (n × n) (n × n) ℂ).trace = Fintype.card n := by
  simp only [Matrix.trace, Matrix.diag, traceMatrix, and_self]
  rw [Fintype.sum_prod_type]
  simp

lemma traceMatrix_square : (traceMatrix : Matrix (n × n) (n × n) ℂ) * traceMatrix =
    (Fintype.card n : ℂ) • traceMatrix := by
  ext p q
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [Matrix.mul_apply, traceMatrix, Fintype.sum_prod_type, hp, hq]

/-- Composing a unital map with the trace map leaves the trace map unchanged. -/
lemma mul_traceMatrix_of_unital (C : Matrix (n × n) (n × n) ℂ)
    (hC : applySuper C 1 = 1) : C * traceMatrix = traceMatrix := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hkl : k = l
  · subst l
    have h := congrArg (fun X : Matrix n n ℂ => X i j) hC
    rw [applySuper_one_entry] at h
    simpa [Matrix.mul_apply, traceMatrix, Fintype.sum_prod_type, Matrix.one_apply] using h
  · simp [Matrix.mul_apply, traceMatrix, hkl]

/-- Self-adjoint unital maps also leave the trace map unchanged on the other side. -/
lemma traceMatrix_mul_of_hermitian_unital (C : Matrix (n × n) (n × n) ℂ)
    (hherm : Cᴴ = C) (hC : applySuper C 1 = 1) : traceMatrix * C = traceMatrix := by
  have h := congrArg Matrix.conjTranspose (mul_traceMatrix_of_unital C hC)
  simpa only [Matrix.conjTranspose_mul, traceMatrix_hermitian, hherm] using h

/-- A pinching supermatrix is unital when its vectors are unit and complete. -/
lemma pinchingMatrix_unital (v : κ → n → ℂ)
    (hnorm : ∀ a, ∑ i, star (v a i) * v a i = 1)
    (hcomplete : ∀ i j, ∑ a, v a i * star (v a j) = if i = j then 1 else 0) :
    applySuper (pinchingMatrix v) 1 = 1 := by
  ext i j
  rw [applySuper_one_entry]
  change (∑ k, ∑ a, v a i * star (v a j) * star (v a k) * v a k) = _
  rw [Finset.sum_comm]
  have hinner (a : κ) :
      (∑ k, v a i * star (v a j) * star (v a k) * v a k) = v a i * star (v a j) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hnorm]
    simp
  simp only [hinner]
  simpa [Matrix.one_apply] using hcomplete i j

omit [DecidableEq n] in
/-- Unit input vectors give the exact trace of a pinching supermatrix. -/
lemma pinchingMatrix_trace (v : κ → n → ℂ)
    (hnorm : ∀ a, ∑ i, star (v a i) * v a i = 1) :
    (pinchingMatrix v).trace = Fintype.card κ := by
  have hexpand : (pinchingMatrix v).trace =
      ∑ a, (∑ i, star (v a i) * v a i) * (∑ j, star (v a j) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, pinchingMatrix]
    rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp only [hnorm, one_mul]
  simp

/-- Six pinching maps in dimension six leave the identity fixed. -/
lemma complementMatrix_unital (v : Fin 6 → κ → Fin 6 → ℂ)
    (hnorm : ∀ r a, ∑ i, star (v r a i) * v r a i = 1)
    (hcomplete : ∀ r i j, ∑ a, v r a i * star (v r a j) = if i = j then 1 else 0) :
    applySuper (complementMatrix v) 1 = 1 := by
  rw [complementMatrix, applySuper_sub_left, applySuper_add_left,
    applySuper_one, applySuper_traceMatrix, applySuper_sum_left]
  simp only [pinchingMatrix_unital _ (hnorm _) (hcomplete _)]
  norm_num [ofNat_smul_eq_nsmul, nsmul_eq_mul]

end MUB6.Weiner

end OAI
