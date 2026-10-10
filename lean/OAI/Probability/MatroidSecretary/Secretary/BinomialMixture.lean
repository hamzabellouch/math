import OAI.Probability.MatroidProphet.Main
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

namespace OAI

namespace MatroidProphet.SecretaryBinomialMixture

open Finset
open scoped NNReal

variable {α : Type*} [DecidableEq α]

/-- A homogeneous Bernoulli mask has the exact cardinality-dependent mass. -/
lemma bitsWeight_const (p : ℝ) (V S : Finset α) (hS : S ⊆ V) :
    bitsWeight (fun _ => p) V S = p ^ S.card * (1 - p) ^ (V.card - S.card) := by
  classical
  unfold bitsWeight
  rw [Finset.prod_ite]
  have hyes : V.filter (fun e => e ∈ S) = S := by
    ext e
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : V.filter (fun e => e ∉ S) = V \ S := by
    ext e
    simp
  rw [hyes, hno, prod_const, prod_const, card_sdiff_of_subset hS]

/-- The cardinality of a predrawn product mask has the full binomial law.
The identity also holds at `p = 0`, `p = 1`, and for an empty ground set. -/
theorem bitsExpectation_card (p : ℝ) (V : Finset α) (f : ℕ → ℝ) :
    bitsExpectation (fun _ => p) V (fun S => f S.card) =
      ∑ k ∈ range (V.card + 1),
        (V.card.choose k : ℝ) * p ^ k * (1 - p) ^ (V.card - k) * f k := by
  classical
  unfold bitsExpectation
  rw [sum_powerset]
  apply sum_congr rfl
  intro k hk
  calc
    (∑ S ∈ V.powersetCard k, bitsWeight (fun _ => p) V S * f S.card) =
        ∑ _S ∈ V.powersetCard k, p ^ k * (1 - p) ^ (V.card - k) * f k := by
      apply sum_congr rfl
      intro S hS
      obtain ⟨hSV, hcard⟩ := mem_powersetCard.mp hS
      rw [bitsWeight_const p V S hSV, hcard]
    _ = (V.card.choose k : ℝ) * p ^ k * (1 - p) ^ (V.card - k) * f k := by
      rw [sum_const, card_powersetCard, nsmul_eq_mul]
      ring

/-- Complete averaging over the binomial prefix length cancels the uniform
fixed-size subset normalizer and recovers the product mask expectation. -/
theorem binomial_uniform_subset_mixture (p : ℝ) (V : Finset α)
    (f : Finset α → ℝ) :
    (∑ k ∈ range (V.card + 1),
      ((V.card.choose k : ℝ) * p ^ k * (1 - p) ^ (V.card - k)) *
        ((V.card.choose k : ℝ)⁻¹ * ∑ S ∈ V.powersetCard k, f S)) =
      bitsExpectation (fun _ => p) V f := by
  classical
  unfold bitsExpectation
  rw [sum_powerset]
  apply sum_congr rfl
  intro k hk
  have hkV : k ≤ V.card := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hc : (V.card.choose k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkV)
  calc
    ((V.card.choose k : ℝ) * p ^ k * (1 - p) ^ (V.card - k)) *
        ((V.card.choose k : ℝ)⁻¹ * ∑ S ∈ V.powersetCard k, f S) =
        (p ^ k * (1 - p) ^ (V.card - k)) * ∑ S ∈ V.powersetCard k, f S := by
      field_simp
    _ = ∑ S ∈ V.powersetCard k, bitsWeight (fun _ => p) V S * f S := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S hS
      obtain ⟨hSV, hcard⟩ := mem_powersetCard.mp hS
      rw [bitsWeight_const p V S hSV, hcard]

/-- Equivalent implementation: predraw a product mask, keep only its cardinality,
then draw a uniform subset of that cardinality independently. -/
theorem predrawn_card_uniform_subset (p : ℝ) (V : Finset α)
    (f : Finset α → ℝ) :
    bitsExpectation (fun _ => p) V
      (fun B => (V.card.choose B.card : ℝ)⁻¹ *
        ∑ S ∈ V.powersetCard B.card, f S) =
      bitsExpectation (fun _ => p) V f := by
  rw [bitsExpectation_card p V (fun k => (V.card.choose k : ℝ)⁻¹ *
    ∑ S ∈ V.powersetCard k, f S)]
  exact binomial_uniform_subset_mixture p V f

open MeasureTheory

/-- The finite binomial law used for the initial prefix-length draw, with its
actual integral rather than an unnormalized formal sum. -/
theorem integral_binomial (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂ProbabilityTheory.binomial n
      ⟨p, p.coe_nonneg, by exact_mod_cast hp⟩) =
      ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) * f k := by
  simpa only [smul_eq_mul, ← Nat.range_succ_eq_Iic] using
    (ProbabilityTheory.integral_binomial (n := n)
      (p := ⟨p, p.coe_nonneg, by exact_mod_cast hp⟩) f)

/-- Sampling the finite binomial length and then a uniform fixed-cardinality
subset gives the homogeneous Bernoulli product mask exactly. -/
theorem integral_binomial_uniform_subset (p : ℝ≥0) (hp : p ≤ 1)
    (V : Finset α) (f : Finset α → ℝ) :
    (∫ k, (V.card.choose k : ℝ)⁻¹ * ∑ S ∈ V.powersetCard k, f S
      ∂ProbabilityTheory.binomial V.card ⟨p, p.coe_nonneg, by exact_mod_cast hp⟩) =
      bitsExpectation (fun _ => (p : ℝ)) V f := by
  rw [integral_binomial p hp V.card (fun k => (V.card.choose k : ℝ)⁻¹ *
    ∑ S ∈ V.powersetCard k, f S)]
  exact binomial_uniform_subset_mixture (p : ℝ) V f

/-- Conversion from the actual finite uniform law to a normalized sum. -/
theorem integral_uniform_fintype {β : Type*} [Fintype β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (f : β → ℝ) :
    (∫ b, f b ∂(PMF.uniformOfFintype β).toMeasure) =
      (Fintype.card β : ℝ)⁻¹ * ∑ b, f b := by
  rw [PMF.integral_eq_sum, mul_sum]
  apply sum_congr rfl
  intro b hb
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]

end MatroidProphet.SecretaryBinomialMixture

end OAI
