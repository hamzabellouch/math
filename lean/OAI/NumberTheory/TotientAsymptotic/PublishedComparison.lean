import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-!
The published comparison input for the conditional collision proof.

Kevin Ford, *The distribution of totients*, Ramanujan J. 2 (1998), 67–151,
revised arXiv:1104.3264v2 (14 July 2013), Lemma 5.1, pp. 21–22.
The published statement permits `k ≥ 1`, including a single surviving
prime. The author-hosted copy also makes this endpoint explicit:
https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf (Lemma 5.1).
We use its specialization with no auxiliary factors (`l = 0`) and with
the entire left shifted product squarefree above the terminal cutoff. The
latter is already part of the application’s good-witness conditions. All its
cutoff, small-remainder, small-cancelled-product and separation hypotheses
are retained here. Its larger smooth-factor exponent is sufficient for the
application; we do not assume the new comparison proposition of the manuscript.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def omegaIn (n : ℕ) (U T : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun (p : ℕ) => U < (p : ℝ) ∧ (p : ℝ) ≤ T)).length

/-- Ford's Definition 1, equations (2.1)–(2.2). -/
def IsNormalPrime (S : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ (omegaIn (p-1) 1 S : ℝ) ≤ 2 * B S ∧
  ∀ U T : ℝ, S ≤ U → U < T → T ≤ (p-1 : ℕ) →
    |(omegaIn (p-1) U T : ℝ) - (B T-B U)| < Real.sqrt (B S * B T)

def SquarefreeAbove (n : ℕ) (Z : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → Z < p → ¬ p^2 ∣ n

def partAbove (n : ℕ) (Z : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun (p : ℕ) => Z < (p : ℝ))).prod

structure ShiftedPair (b : ℕ) where
  left : Fin b → ℕ
  right : Fin b → ℕ
  remainder : ℕ

def shiftedProduct {b : ℕ} (p : Fin b → ℕ) : ℕ := ∏ i, (p i-1)

def FordComparisonConditions (b : ℕ) (y S : ℝ) (D r : ℕ)
    (Y U : ℕ → ℝ) (t : ShiftedPair b) : Prop :=
  0 < t.remainder ∧
  (∀ j : Fin b,
    IsNormalPrime S (t.left j) ∧ IsNormalPrime S (t.right j) ∧
    t.left j ≠ t.right j ∧
    U j ≤ largestPrimeFactor (t.left j-1) ∧
    (largestPrimeFactor (t.left j-1) : ℝ) ≤ Y j ∧
    U j ≤ largestPrimeFactor (t.right j-1) ∧
    (largestPrimeFactor (t.right j-1) : ℝ) ≤ Y j ∧
    SquarefreeAbove (t.left j-1) (Y b) ∧
    SquarefreeAbove (t.right j-1) (Y b)) ∧
  D * shiftedProduct t.left = t.remainder * shiftedProduct t.right ∧
  (D * shiftedProduct t.left : ℕ) ≤ y / r ∧
  (largestPrimeFactor t.remainder : ℝ) ≤ Y b ∧
  (∀ hb : 0 < b, (partAbove (t.left ⟨0, hb⟩-1) (Y 1) : ℝ) > Real.sqrt y) ∧
  SquarefreeAbove (shiftedProduct t.left) (Y b)

/-- The cutoff and size restrictions of Ford's published lemma. -/
def FordComparisonParameters (b : ℕ) (y S : ℝ) (D r : ℕ) (Y U : ℕ → ℝ) : Prop :=
  1 ≤ b ∧ Y 0 = y ∧ Real.exp (Real.exp 1) ≤ S ∧ S ≤ Y b ∧
  (∀ j ∈ Finset.range b, Y (j+1) < U j ∧ U j < Y j) ∧
  Y 1 ≤ y ^ (1 / (10 * B y)) ∧
  (∀ j ∈ Finset.Icc 2 b, 2 * Real.sqrt (B S / B y) <
    B (Y (j-1)) / B y - B (Y j) / B y) ∧
  1 ≤ D ∧ (D : ℝ) ≤ y ^ (1/100 : ℝ) ∧
  (largestPrimeFactor D : ℝ) ≤ Y b ∧
  1 ≤ r ∧ (r : ℝ) ≤ y ^ (1/10 : ℝ)

def comparisonError (b : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.Icc 1 (b-1), (B (Y j) / B y - B (U j) / B y) +
    Real.sqrt (B S / B y) * ∑ i ∈ Finset.Icc 2 b,
      ((i : ℝ) * Real.log i + i)

def fordComparisonBound (C : ℝ) (b : ℕ) (y S : ℝ) (D r : ℕ)
    (Y U : ℕ → ℝ) : ℝ :=
  y / (D*r) * (C * B y)^(6*b) * (b+1 : ℝ)^D.primeFactorsList.length *
    (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1) *
    (Real.log y)^(-2 + (∑ j ∈ Finset.Icc 1 (b-1), a j * (B (Y j) / B y)) +
      comparisonError b y S Y U)


def FordLemma51Input : Prop :=
  ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ (b : ℕ) (y S : ℝ) (D r : ℕ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters b y S D r Y U →
      ∀ T : Finset (ShiftedPair b),
        (∀ t ∈ T, FordComparisonConditions b y S D r Y U t) →
        (T.card : ℝ) ≤ fordComparisonBound C b y S D r Y U

lemma squarefreeAbove_of_dvd {m n : ℕ} {Z : ℝ}
    (hmn : m ∣ n) (hn : SquarefreeAbove n Z) : SquarefreeAbove m Z := by
  intro p hp hpZ hpm
  exact hn p hp hpZ (hpm.trans hmn)

lemma shifted_factor_dvd {b : ℕ} (p : Fin b → ℕ) (i : Fin b) :
    p i-1 ∣ shiftedProduct p :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

lemma squarefree_shifts_of_common_product {b D : ℕ} (t : ShiftedPair b) (Z : ℝ)
    (heq : D * shiftedProduct t.left = t.remainder * shiftedProduct t.right)
    (hsq : SquarefreeAbove (D * shiftedProduct t.left) Z) (i : Fin b) :
    SquarefreeAbove (t.left i-1) Z ∧ SquarefreeAbove (t.right i-1) Z := by
  constructor
  · exact squarefreeAbove_of_dvd ((shifted_factor_dvd t.left i).trans (dvd_mul_left _ _)) hsq
  · have hr : t.right i-1 ∣ t.remainder * shiftedProduct t.right :=
      (shifted_factor_dvd t.right i).trans (dvd_mul_left _ _)
    rw [← heq] at hr
    exact squarefreeAbove_of_dvd hr hsq

end TotientAsymptotic

end

end OAI
