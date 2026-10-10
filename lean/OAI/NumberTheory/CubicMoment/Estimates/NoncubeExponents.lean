import Mathlib

namespace OAI

/-! Strict exponent gaps away from the two exceptional conductor shapes.
These are the normalized exponents of the two cubic-sieve bounds and
of the ordinary character large sieve, respectively. -/

noncomputable section

namespace CubicFirstMoment

def pSieveExponent (p q : ℝ) : ℝ :=
  max ((2*p+q)/3-1) (max ((q-p)/3) ((p+q-1)/3))

def qSieveExponent (p q : ℝ) : ℝ :=
  max ((2*p+q)/3-1) (max (2*(p-q)/3) ((2*p-1)/3))

def ordinarySieveExponent (p q : ℝ) : ℝ :=
  max (-(p+2*q)/3) ((5*p+4*q)/3-1)

def noncubeSieveExponent (p q : ℝ) : ℝ :=
  min (pSieveExponent p q) (min (qSieveExponent p q) (ordinarySieveExponent p q))

lemma pSieveExponent_neg {p q : ℝ} (hpq : q < p) (hq : 0 ≤ q)
    (hsize : p+2*q ≤ 1) (hex : p ≠ 1 ∨ q ≠ 0) :
    pSieveExponent p q < 0 := by
  have hsum : p+q < 1 := by
    by_contra! hn
    have hq0 : q = 0 := by linarith
    have hp1 : p = 1 := by linarith
    rcases hex with h | h
    · exact h hp1
    · exact h hq0
  unfold pSieveExponent
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

lemma qSieveExponent_neg {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q)
    (hsize : p+2*q ≤ 1) : qSieveExponent p q < 0 := by
  unfold qSieveExponent
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

lemma ordinarySieveExponent_diag_neg {v : ℝ} (hv : 0 < v) (hv1 : v < 1/3) :
    ordinarySieveExponent v v < 0 := by
  unfold ordinarySieveExponent
  exact max_lt (by linarith) (by linarith)

/-- The only nonnegative-gap possibilities in the large-conductor region
are precisely the two shapes treated by the structured moment argument. -/
theorem noncubeSieveExponent_neg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsize : p+2*q ≤ 1) (hlarge : 0 < p+2*q)
    (hfirst : p ≠ 1 ∨ q ≠ 0) (hbalanced : p ≠ 1/3 ∨ q ≠ 1/3) :
    noncubeSieveExponent p q < 0 := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact lt_of_le_of_lt (min_le_right _ _)
      (lt_of_le_of_lt (min_le_left _ _) (qSieveExponent_neg hp hpq hsize))
  · subst q
    have hp0 : 0 < p := by linarith
    have hp1 : p < 1/3 := by
      rcases hbalanced with h | h <;> exact lt_of_le_of_ne (by linarith) h
    exact lt_of_le_of_lt (min_le_right _ _)
      (lt_of_le_of_lt (min_le_right _ _) (ordinarySieveExponent_diag_neg hp0 hp1))
  · exact lt_of_le_of_lt (min_le_left _ _) (pSieveExponent_neg hpq hq hsize hfirst)

lemma continuous_noncubeSieveExponent :
    Continuous (fun x : ℝ × ℝ => noncubeSieveExponent x.1 x.2) := by
  unfold noncubeSieveExponent pSieveExponent qSieveExponent ordinarySieveExponent
  fun_prop

end CubicFirstMoment

end

end OAI
