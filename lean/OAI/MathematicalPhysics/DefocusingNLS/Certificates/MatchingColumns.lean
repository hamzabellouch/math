import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeMatching
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace OAI

/-!
# Division-free backward matching

The tail recurrences imply the matrix identity in Lemma `free:columns` of
*Stable self-similar blowup for a supercritical defocusing Schrödinger equation
on the torus* (September 2026), including at zeros of the Pochhammer factor.
-/

open Matrix

namespace DefocusingNLS

/-- One backward step, with `t = q + n` and `d = t - M`. -/
noncomputable def backwardMatrix (M s t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![t - M - s, -s; t, t]

/-- The ordered product `F₀ ⋯ Fₖ₋₁`. -/
noncomputable def backwardProduct (M s q : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | k + 1 => backwardProduct M s q k * backwardMatrix M s (q + k)

/-- The backward recurrence requires no division by `t` or `t - M`. -/
theorem backwardMatrix_step (M s t B C B' C' : ℂ)
    (hB : (t - M) * B' = t * B + s * C)
    (hC : C' = C - B') :
    backwardMatrix M s t *ᵥ ![B', C'] = t • ![B, C] := by
  ext i
  fin_cases i
  · simp [backwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hC]
    linear_combination hB
  · simp [backwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hC]
    ring

/-- Multiplication of the division-free recurrences gives precisely the
Pochhammer factor, including at its zeros. -/
theorem backwardProduct_apply (M s q : ℂ) (B C : ℕ → ℂ)
    (hB : ∀ n, (q + n - M) * B (n + 1) = (q + n) * B n + s * C n)
    (hC : ∀ n, C (n + 1) = C n - B (n + 1)) (k : ℕ) :
    backwardProduct M s q k *ᵥ ![B k, C k] =
      (ascPochhammer ℂ k).eval q • ![B 0, C 0] := by
  induction k with
  | zero => simp [backwardProduct]
  | succ k ih =>
    rw [backwardProduct, ← Matrix.mulVec_mulVec,
      backwardMatrix_step M s (q + k) _ _ _ _ (hB k) (hC k),
      Matrix.mulVec_smul, ih, smul_smul, ascPochhammer_succ_eval]
    rw [mul_comm (q + k)]

/-- In the relevant half-plane the only Pochhammer zero is `q = 0`. -/
theorem pochhammer_zero_iff (q : ℂ) (k : ℕ) (hk : 0 < k)
    (hq : -1 < q.re) : (ascPochhammer ℂ k).eval q = 0 ↔ q = 0 := by
  constructor
  · intro h
    obtain ⟨n, _, hn⟩ := (ascPochhammer_eval_eq_zero_iff k q).mp h
    have hre := congrArg Complex.re hn
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hnlt : (n : ℝ) < 1 := by linarith
    have hnzero : n = 0 := by
      have : n < 1 := by exact_mod_cast hnlt
      omega
    simpa [hnzero] using hn.symm
  · rintro rfl
    exact ascPochhammer_ne_zero_eval_zero ℂ hk.ne'

end DefocusingNLS

end OAI
