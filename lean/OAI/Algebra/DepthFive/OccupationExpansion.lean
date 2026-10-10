import OAI.Algebra.DepthFive.OccupationSum
import OAI.Algebra.DepthFive.OccupationComparison

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- A finite expansion in the multivariate falling-factorial basis. -/
def factorialExpansionValue {ι J : Type*} [Fintype ι]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (M : ι →₀ ℕ) : ℝ :=
  ∑ j ∈ s, c j * ∏ i, ((M i).descFactorial (d j i) : ℝ)

/-- The corresponding product-geometric factorial-moment expression. -/
def geometricExpansionValue {ι J : Type*} [Fintype ι]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (G : ℝ) : ℝ :=
  ∑ j ∈ s, (c j * ∏ i, (d j i).factorial : ℝ) * G ^ (∑ i, d j i)

/-- Average over the finite uniform weak-composition space. -/
def compositionExpansionMean {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (t : ℕ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      factorialExpansionValue s c d M) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card

/-- Linearity and the exact occupation factorial-moment identity. -/
theorem compositionExpansionMean_eq {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (t : ℕ) :
    compositionExpansionMean s c d t =
      ∑ j ∈ s, (c j * ∏ i, (d j i).factorial : ℝ) *
        ((t.descFactorial (∑ i, d j i) : ℝ) /
          ((Fintype.card ι).ascFactorial (∑ i, d j i) : ℝ)) := by
  unfold compositionExpansionMean factorialExpansionValue
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, mul_div_assoc, occupation_factorial_moment]
  push_cast
  ring

/-- Upper geometric comparison, including zero total occupation and arbitrary orders. -/
theorem compositionExpansionMean_le_geometric {ι J : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ)
    (t : ℕ) (hc : ∀ j ∈ s, 0 ≤ c j) :
    compositionExpansionMean s c d t ≤
      geometricExpansionValue s c d ((t : ℝ) / Fintype.card ι) := by
  rw [compositionExpansionMean_eq]
  apply weighted_factorialMoment_sum_le s _ _ Fintype.card_pos
  intro j hj
  exact mul_nonneg (hc j hj) (by positivity)

/-- The lower geometric comparison depends only on a uniform total-order bound. -/
theorem exp_mul_geometric_le_compositionExpansionMean {ι J : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ)
    {t H : ℕ} (ht : 0 < t) (hH : 2 * H ≤ t) (hc : ∀ j ∈ s, 0 ≤ c j)
    (hd : ∀ j ∈ s, ∑ i, d j i ≤ H) :
    Real.exp (-(H : ℝ) ^ 2 / t - (H : ℝ) ^ 2 / (2 * Fintype.card ι)) *
      geometricExpansionValue s c d ((t : ℝ) / Fintype.card ι) ≤
        compositionExpansionMean s c d t := by
  rw [compositionExpansionMean_eq]
  apply exp_mul_weighted_mean_sum_le s _ _ ht Fintype.card_pos hH _ hd
  intro j hj
  exact mul_nonneg (hc j hj) (by positivity)

/-- Uniform averages in two independent weak-composition groups, with a shared term index. -/
def twoGroupCompositionExpansionMean {ι κ J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (s : Finset J) (c : J → ℝ)
    (d : J → ι → ℕ) (e : J → κ → ℕ) (a b : ℕ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
    compositionExpansionMean s
      (fun j => c j * ∏ i, ((M i).descFactorial (d j i) : ℝ)) e b) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card

/-- The product-geometric expression for a two-group factorial expansion. -/
def twoGroupGeometricExpansionValue {ι κ J : Type*} [Fintype ι] [Fintype κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ)
    (A B : ℝ) : ℝ :=
  ∑ j ∈ s, (c j * (∏ i, (d j i).factorial : ℝ) * (∏ i, (e j i).factorial : ℝ)) *
    (A ^ (∑ i, d j i) * B ^ (∑ i, e j i))

theorem twoGroupCompositionExpansionMean_eq {ι κ J : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ) (a b : ℕ) :
    twoGroupCompositionExpansionMean s c d e a b =
      ∑ j ∈ s, (c j * (∏ i, (d j i).factorial : ℝ) * (∏ i, (e j i).factorial : ℝ)) *
        (((a.descFactorial (∑ i, d j i) : ℝ) /
          ((Fintype.card ι).ascFactorial (∑ i, d j i) : ℝ)) *
         ((b.descFactorial (∑ i, e j i) : ℝ) /
          ((Fintype.card κ).ascFactorial (∑ i, e j i) : ℝ))) := by
  unfold twoGroupCompositionExpansionMean
  simp_rw [compositionExpansionMean_eq]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (c j * (∏ i, (e j i).factorial : ℝ) *
          ((b.descFactorial (∑ i, e j i) : ℝ) /
            ((Fintype.card κ).ascFactorial (∑ i, e j i) : ℝ))) *
        ((∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
          ∏ i, ((M i).descFactorial (d j i) : ℝ)) /
            (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card) := by
      simp only [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M hM
      push_cast
      ring
    _ = _ := by
      rw [occupation_factorial_moment]
      ring

/-- Actual upper occupation comparison for nonnegative two-group expansions. -/
theorem twoGroupCompositionExpansionMean_le_geometric {ι κ J : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ) (a b : ℕ)
    (hc : ∀ j ∈ s, 0 ≤ c j) :
    twoGroupCompositionExpansionMean s c d e a b ≤
      twoGroupGeometricExpansionValue s c d e
        ((a : ℝ) / Fintype.card ι) ((b : ℝ) / Fintype.card κ) := by
  rw [twoGroupCompositionExpansionMean_eq]
  apply weighted_two_group_factorialMoment_sum_le s _ _ _
    Fintype.card_pos Fintype.card_pos
  intro j hj
  exact mul_nonneg (mul_nonneg (hc j hj) (by positivity)) (by positivity)

/-- Actual uniform lower occupation comparison for nonnegative two-group expansions. -/
theorem exp_mul_geometric_le_twoGroupCompositionExpansionMean {ι κ J : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ)
    {a b H J₀ : ℕ} (ha : 0 < a) (hb : 0 < b) (hH : 2 * H ≤ a) (hJ : 2 * J₀ ≤ b)
    (hc : ∀ j ∈ s, 0 ≤ c j) (hd : ∀ j ∈ s, ∑ i, d j i ≤ H)
    (he : ∀ j ∈ s, ∑ i, e j i ≤ J₀) :
    Real.exp ((-(H : ℝ) ^ 2 / a - (H : ℝ) ^ 2 / (2 * Fintype.card ι)) +
        (-(J₀ : ℝ) ^ 2 / b - (J₀ : ℝ) ^ 2 / (2 * Fintype.card κ))) *
      twoGroupGeometricExpansionValue s c d e
        ((a : ℝ) / Fintype.card ι) ((b : ℝ) / Fintype.card κ) ≤
      twoGroupCompositionExpansionMean s c d e a b := by
  rw [twoGroupCompositionExpansionMean_eq]
  apply exp_mul_weighted_two_group_mean_sum_le s _ _ _
    ha Fintype.card_pos hb Fintype.card_pos hH hJ _ hd he
  intro j hj
  exact mul_nonneg (mul_nonneg (hc j hj) (by positivity)) (by positivity)

end Problem335

end

end OAI
