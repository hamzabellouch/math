import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Exact correction by a finite residual mixture

Finite probability arithmetic gives the residual correction used in exact
sampling. The construction is that of Göbel, Liu, Manurangsi and Pappik,
*Perfect sampling from rapidly mixing Markov chains*, arXiv:2410.00882v2
(2024), §3.1, Algorithm 1 and Theorem 6.

All probabilities are rational, as required for the finite fair-bit sampler.
-/

open scoped BigOperators

namespace ContingencyTables.ResidualMixture

variable {α : Type*} [Fintype α]

/-- A finite probability law with exactly represented rational masses. -/
structure RationalLaw (α : Type*) [Fintype α] where
  mass : α → ℚ
  nonnegative : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

variable [Nonempty α]

lemma card_pos : (0 : ℚ) < Fintype.card α := by
  exact_mod_cast Fintype.card_pos

/-- The uniform mass on a nonempty finite space. -/
def uniformMass : ℚ := 1 / Fintype.card α

lemma uniformMass_pos : 0 < uniformMass (α := α) := by
  exact div_pos (by norm_num) card_pos

lemma uniformMass_total : ∑ _x : α, uniformMass (α := α) = 1 := by
  simp only [uniformMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel (ne_of_gt card_pos)

/-- The residual point mass used on the rare correction branch. -/
def residualMass (p : RationalLaw α) (δ : ℚ) (x : α) : ℚ :=
  (uniformMass (α := α) - (1 - δ) * p.mass x) / δ

/-- The pointwise approximation and cardinality bound imply domination.
This is the estimate immediately before the definition of `r(z)` in 200-01. -/
lemma approximate_domination (p : RationalLaw α) {δ : ℚ}
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hcard : (Fintype.card α : ℚ) * δ ≤ 1)
    (happrox : ∀ x, p.mass x ≤ uniformMass (α := α) + δ ^ 2) (x : α) :
    (1 - δ) * p.mass x ≤ uniformMass (α := α) := by
  have hδu : δ ≤ uniformMass (α := α) := by
    rw [uniformMass, le_div_iff₀ card_pos]
    nlinarith [hcard]
  have hmul := mul_le_mul_of_nonneg_left (happrox x) (sub_nonneg.mpr hδone)
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have herr : (1 - δ) * δ ^ 2 ≤ δ * uniformMass (α := α) := by
    have hfirst := mul_le_mul_of_nonneg_left hδsq (sub_nonneg.mpr hδone)
    have hsecond := mul_le_mul_of_nonneg_left hδu (le_of_lt hδ)
    nlinarith [hfirst, hsecond]
  nlinarith [hmul, herr]

omit [Nonempty α] in
lemma residualMass_nonnegative (p : RationalLaw α) {δ : ℚ} (hδ : 0 < δ)
    (hdom : ∀ x, (1 - δ) * p.mass x ≤ uniformMass (α := α)) (x : α) :
    0 ≤ residualMass p δ x := by
  exact div_nonneg (sub_nonneg.mpr (hdom x)) (le_of_lt hδ)

lemma residualMass_total (p : RationalLaw α) {δ : ℚ} (hδ : δ ≠ 0) :
    ∑ x, residualMass p δ x = 1 := by
  simp only [residualMass, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, uniformMass_total, p.total]
  field_simp
  ring

/-- A residual law exists whenever the ordinary branch is pointwise dominated
by the target law. No additional existence assumption is used. -/
def residualLaw (p : RationalLaw α) {δ : ℚ} (hδ : 0 < δ)
    (hdom : ∀ x, (1 - δ) * p.mass x ≤ uniformMass (α := α)) : RationalLaw α where
  mass := residualMass p δ
  nonnegative := residualMass_nonnegative p hδ hdom
  total := residualMass_total p (ne_of_gt hδ)

omit [Nonempty α] in
/-- The two branches combine to give exactly uniform point masses. -/
theorem mixture_exact (p : RationalLaw α) {δ : ℚ} (hδ : δ ≠ 0) (x : α) :
    (1 - δ) * p.mass x + δ * residualMass p δ x = uniformMass (α := α) := by
  dsimp [residualMass]
  field_simp
  ring

/-- The complete finite residual-mixture consequence of the pointwise
approximation bound used by the manuscript. -/
theorem exact_correction (p : RationalLaw α) {δ : ℚ}
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hcard : (Fintype.card α : ℚ) * δ ≤ 1)
    (happrox : ∀ x, p.mass x ≤ uniformMass (α := α) + δ ^ 2) :
    ∃ r : RationalLaw α, ∀ x,
      (1 - δ) * p.mass x + δ * r.mass x = uniformMass (α := α) := by
  refine ⟨residualLaw p hδ (approximate_domination p hδ hδone hcard happrox), ?_⟩
  exact mixture_exact p (ne_of_gt hδ)

/-- The integer numerator in equation `eq:residual-integers` of 200-01.
Here `Q = 2^R`, `T = 2^D`, and `a x` is the tabulated dyadic numerator. -/
def residualNumerator (Q T : ℤ) (a : α → ℤ) (x : α) : ℤ :=
  Q * T - (Fintype.card α : ℤ) * (T - 1) * a x

omit [Nonempty α] in
/-- The residual integer weights have the exact required total. -/
lemma residualNumerator_total (Q T : ℤ) (a : α → ℤ) (ha : ∑ x, a x = Q) :
    ∑ x, residualNumerator Q T a x = (Fintype.card α : ℤ) * Q := by
  simp only [residualNumerator, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ha]
  ring

/-- The numerator realizes the residual law exactly as a rational quotient. -/
lemma residualNumerator_quotient (Q T : ℤ) (a : α → ℤ)
    (hQ : Q ≠ 0) (hT : T ≠ 0) (x : α) :
    (residualNumerator Q T a x : ℚ) /
        ((Fintype.card α : ℚ) * Q) =
      (uniformMass (α := α) - (1 - 1 / (T : ℚ)) * ((a x : ℚ) / Q)) /
        (1 / (T : ℚ)) := by
  have hQc : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hTc : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  have hc : (Fintype.card α : ℚ) ≠ 0 := ne_of_gt card_pos
  simp only [residualNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_one, uniformMass]
  field_simp

/-- Pointwise domination makes the actual integer correction weights
nonnegative, so their cumulative sums define a finite exact draw. -/
lemma residualNumerator_nonnegative {Q T : ℤ} (a : α → ℤ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hdom : ∀ x, (1 - 1 / (T : ℚ)) * ((a x : ℚ) / Q) ≤
      uniformMass (α := α)) (x : α) :
    0 ≤ residualNumerator Q T a x := by
  have hQc : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hTc : (0 : ℚ) < T := by exact_mod_cast hT
  have hres : (0 : ℚ) ≤
      (uniformMass (α := α) - (1 - 1 / (T : ℚ)) * ((a x : ℚ) / Q)) /
        (1 / (T : ℚ)) :=
    div_nonneg (sub_nonneg.mpr (hdom x)) (le_of_lt (one_div_pos.mpr hTc))
  rw [← residualNumerator_quotient Q T a (ne_of_gt hQ) (ne_of_gt hT) x] at hres
  have hden : (0 : ℚ) < (Fintype.card α : ℚ) * Q := mul_pos card_pos hQc
  have hnum : (0 : ℚ) ≤ residualNumerator Q T a x :=
    by simpa using (le_div_iff₀ hden).mp hres
  exact_mod_cast hnum

/-- Acceptance of a dyadic proposal has probability greater than one half
when the proposal range is less than twice the target range. This is the
probability estimate for the manuscript's exact integer rejection draw. -/
lemma integer_rejection_acceptance {V Q : ℕ} (hV : 0 < V)
    (hcover : V ≤ Q) (hshort : Q < 2 * V) :
    (1 / 2 : ℚ) < (V : ℚ) / Q ∧ (V : ℚ) / Q ≤ 1 := by
  have hQ : (0 : ℚ) < Q := by exact_mod_cast lt_of_lt_of_le hV hcover
  have hcover' : (V : ℚ) ≤ Q := by exact_mod_cast hcover
  have hshort' : (Q : ℚ) < 2 * V := by exact_mod_cast hshort
  constructor
  · rw [lt_div_iff₀ hQ]
    nlinarith
  · exact (div_le_iff₀ hQ).mpr (by simpa using hcover')

/-- A branch with probability `δ` and conditional cost `correction` adds at
most the permitted rare-branch allowance to the ordinary cost bound. -/
lemma expected_cost_bound {δ ordinary correction allowance : ℚ}
    (hδ : 0 ≤ δ) (hordinary : 0 ≤ ordinary)
    (hrare : δ * correction ≤ allowance) :
    (1 - δ) * ordinary + δ * correction ≤ ordinary + allowance := by
  have hprod := mul_nonneg hδ hordinary
  nlinarith

end ContingencyTables.ResidualMixture

end OAI
