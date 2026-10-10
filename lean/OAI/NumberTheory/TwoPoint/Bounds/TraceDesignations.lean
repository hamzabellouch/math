import OAI.NumberTheory.TwoPoint.Bounds.LitConsistency

namespace OAI

/-! Exact lit-consistency reduction and centering for a designated trace word. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
/-- Expand only the designated nonsingleton occurrences, retaining all signs. -/
lemma centered_occurrence_expansion [DecidableEq τ] (S : Finset τ)
    (label : τ → ι) (target : τ → A) (θ : ι → ℝ) (x : ι → A) :
    (∏ t ∈ S, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) =
      ∑ U ∈ S.powerset, ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t)) *
        ∏ t ∈ S \ U, if x (label t) = target t then (1 : ℝ) else 0 := by
  rw [Finset.prod_sub]
  apply sum_congr rfl
  intro U _
  ring

/-- The signed finite expansion is integrated before taking absolute values. -/
lemma centered_occurrence_expectation [DecidableEq τ] (μ : FiniteLaw (ι → A))
    (S : Finset τ) (label : τ → ι) (target : τ → A) (θ : ι → ℝ)
    (F : (ι → A) → ℝ) :
    μ.average (fun x =>
      (∏ t ∈ S, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) * F x) =
      ∑ U ∈ S.powerset, μ.average (fun x =>
        ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t)) *
          ((∏ t ∈ S \ U, if x (label t) = target t then (1 : ℝ) else 0) * F x)) := by
  simp only [FiniteLaw.average]
  simp_rw [centered_occurrence_expansion S label target θ, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro x _
  ring

/-- A contradictory pair of lit offsets annihilates the term exactly. -/
lemma designated_residue_zero (μ : ι → FiniteLaw A) (S : Finset ι) (L : Finset τ)
    (label : τ → ι) (target : τ → A) (a : ι → A) (c : ℝ) (F : (ι → A) → ℝ)
    (hL : ¬LitConsistent L label target) :
    (FiniteLaw.independent μ).average (fun x => c *
      ((∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) *
        ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x))) = 0 := by
  simp only [lit_indicator_product_eq_zero L label target hL, zero_mul, mul_zero]
  exact FiniteLaw.average_const _ 0

/-- This is the designated-term mixed-difference bound with literal lit
occurrences, including the scalar sign and every residue-independent factor. -/
theorem designated_residue_bound (μ : ι → FiniteLaw A) (S : Finset ι) (L : Finset τ)
    (label : τ → ι) (target : τ → A) (a base : ι → A) (c : ℝ) (F : (ι → A) → ℝ)
    (hL : LitConsistent L label target) (hSL : Disjoint S (L.image label)) :
    |(FiniteLaw.independent μ).average (fun x => c *
      ((∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) *
        ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x)))| ≤
      |c| * (∏ i ∈ L.image label, (μ i).weight (litForcedTarget L label target base i)) *
        (∏ i ∈ S, (μ i).weight (a i)) *
          (FiniteLaw.independent μ).average (fun x =>
            |selectedMixedDifference S a
              (fun x => F (forceCoordinates (L.image label) (litForcedTarget L label target base) x)) x|) := by
  simp_rw [lit_indicator_product L label target base hL]
  rw [FiniteLaw.average_const_mul, abs_mul]
  calc
    _ ≤ |c| * ((∏ i ∈ L.image label, (μ i).weight (litForcedTarget L label target base i)) *
        (∏ i ∈ S, (μ i).weight (a i)) *
          (FiniteLaw.independent μ).average (fun x =>
            |selectedMixedDifference S a
              (fun x => F (forceCoordinates (L.image label) (litForcedTarget L label target base) x)) x|)) :=
      mul_le_mul_of_nonneg_left (FiniteLaw.selected_designation_bound μ S (L.image label) hSL a
        (litForcedTarget L label target base) F) (abs_nonneg c)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
