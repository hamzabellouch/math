import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

/-!
# Algebra in the free exterior matching problem

The finite-dimensional cone identity in
*Stable self-similar blowup for a supercritical defocusing Schrödinger equation
on the torus* (September 2026), Lemma `free:laguerre`, follows algebraically
from the Laguerre recurrence.
-/

open Filter Topology

namespace DefocusingNLS

/-- The real cone form in equation `free:cone-form`. -/
noncomputable def coneForm (M : ℝ) (s B C : ℂ) : ℝ :=
  M / 2 * Complex.normSq B + (s * star B * C).re

/-- The Laguerre recurrence implies its exact cone increment. -/
theorem coneForm_increment (M : ℝ) (s t B C g : ℂ)
    (hs : s.re = 0)
    (hrec : t * g = -(M : ℂ) * (B - g) - s * C) :
    coneForm M s (B - g) (C - (B - g)) - coneForm M s B C =
      (t.re - M / 2) * Complex.normSq g := by
  have hr := congrArg Complex.re hrec
  have hi := congrArg Complex.im hrec
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, hs,
    zero_mul, zero_sub, zero_add] at hr hi
  simp only [coneForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im, hs,
    zero_mul, zero_sub, zero_add]
  linear_combination -g.re * hr - g.im * hi

/-- With the paper's mode parameters, the angular degree cancels from the increment. -/
theorem mode_coneForm_increment (σ : ℝ) (ℓ n : ℕ) (s t B C g : ℂ)
    (hs : s.re = 0) (ht : t.re = σ + (ℓ : ℝ) / 2 + n)
    (hrec : t * g = -((ℓ : ℝ) + 5 : ℂ) * (B - g) - s * C) :
    coneForm ((ℓ : ℝ) + 5) s (B - g) (C - (B - g)) -
      coneForm ((ℓ : ℝ) + 5) s B C =
        (σ + n - 5 / 2) * Complex.normSq g := by
  have hrec' : t * g = -(((ℓ : ℝ) + 5 : ℝ) : ℂ) * (B - g) - s * C := by
    simpa using hrec
  rw [coneForm_increment ((ℓ : ℝ) + 5) s t B C g hs hrec', ht]
  ring

/-- The cone increments past index three are nonnegative in the counting half-plane. -/
theorem mode_increment_nonneg (σ : ℝ) (n : ℕ) (g : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hn : 3 ≤ n) :
    0 ≤ (σ + n - 5 / 2) * Complex.normSq g := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hweight : 0 ≤ σ + n - 5 / 2 := by linarith
  exact mul_nonneg hweight (Complex.normSq_nonneg g)

/-- Completing the square identifies the cone with the tail disk. -/
theorem coneForm_square_identity (M : ℝ) (s B C : ℂ) :
    Complex.normSq ((M : ℂ) * B + s * C) - Complex.normSq (s * C) =
      2 * M * coneForm M s B C := by
  simp only [coneForm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A strictly negative cone form implies both a nonzero denominator and the
strict disk bound used in Lemma `free:cone`. The purely imaginary specialization
`s = h * I * Z` has disk center `-s / M` and radius `Z / M`. -/
theorem tail_disk_of_negative_cone (M : ℝ) (s B C : ℂ)
    (hM : 0 < M) (hcone : coneForm M s B C < 0) :
    C ≠ 0 ∧ Complex.normSq (B / C + s / (M : ℂ)) <
      Complex.normSq (s / (M : ℂ)) := by
  have hC : C ≠ 0 := by
    intro hzero
    have hn := Complex.normSq_nonneg B
    simp only [hzero, coneForm, mul_zero, Complex.zero_re, add_zero] at hcone
    nlinarith
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hnegative : 2 * M * coneForm M s B C < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hcone
  have hdisk : Complex.normSq ((M : ℂ) * B + s * C) < Complex.normSq (s * C) := by
    linarith [coneForm_square_identity M s B C]
  refine ⟨hC, ?_⟩
  have hquot : B / C + s / (M : ℂ) =
      ((M : ℂ) * B + s * C) / ((M : ℂ) * C) := by
    field_simp [hC, hMc]
  have hcenter : s / (M : ℂ) = s * C / ((M : ℂ) * C) := by
    field_simp [hC, hMc]
  rw [hquot, hcenter, Complex.normSq_div, Complex.normSq_div]
  exact div_lt_div_of_pos_right hdisk (Complex.normSq_pos.mpr (mul_ne_zero hMc hC))

/-- Increasing cone forms that tend to zero are nonpositive; one nonzero
positive-weight increment makes the initial cone strictly negative. -/
theorem negative_of_increasing_tail {p : ℕ → ℝ} (K : ℕ)
    (hlimit : Tendsto p atTop (𝓝 0))
    (hinc : ∀ n, K ≤ n → p n ≤ p (n + 1))
    (hstrict : ∃ n, K ≤ n ∧ p n < p (n + 1)) : p K < 0 := by
  have hmono : Monotone (fun n => p (n + K)) := by
    apply monotone_nat_of_le_succ
    intro n
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hinc (n + K) (Nat.le_add_left K n)
  have hzero (n : ℕ) : p (n + K) ≤ 0 :=
    hmono.ge_of_tendsto (hlimit.comp (tendsto_add_atTop_nat K)) n
  obtain ⟨n, hn, hstrict⟩ := hstrict
  have hKn : p K ≤ p n := by
    simpa [Nat.sub_add_cancel hn] using hmono (Nat.zero_le (n - K))
  have hnzero : p (n + 1) ≤ 0 := by
    simpa [Nat.sub_add_cancel (show K ≤ n + 1 by omega)] using hzero (n + 1 - K)
  exact lt_of_le_of_lt hKn (lt_of_lt_of_le hstrict hnzero)

end DefocusingNLS

end OAI
