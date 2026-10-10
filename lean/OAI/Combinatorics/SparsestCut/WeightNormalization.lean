/-
Copyright (c) 2026 OpenAI. All rights reserved.
Authors: OpenAI
-/
import OAI.Combinatorics.SparsestCut.FiniteWeights
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-!
# Normalization of finite weights

A lower approximation to a probability law retains coordinatewise domination and
setwise lower bounds after normalization. These are the retained-demand estimates
in Section 7 of OpenAI's *Constant-factor hardness of uniform sparsest cut*.
-/

open scoped BigOperators

namespace UniformSparsestCut.FiniteWeights

variable {ι : Type*} [Fintype ι]

noncomputable def normalized (l : ι → ℝ) : ι → ℝ := fun i => l i / total l

theorem normalized_nonneg {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hL : 0 < total l) :
    ∀ i, 0 ≤ normalized l i :=
  fun i => div_nonneg (hl i) hL.le

theorem normalized_total {l : ι → ℝ} (hL : 0 < total l) : total (normalized l) = 1 := by
  change (∑ i, l i / total l) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hL)

theorem normalized_mass (l : ι → ℝ) (h : ι → Bool) :
    mass (normalized l) h = mass l h / total l := by
  change (∑ i, l i / total l * indicator (h i)) = mass l h / total l
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rfl

/-- Normalization of a sufficiently large lower approximation increases each weight
by at most a factor of two. -/
theorem normalized_le_twice {μ l : ι → ℝ} {ε : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hle : ∀ i, l i ≤ μ i)
    (hε : ε ≤ 1 / 2) (hL : 1 - ε ≤ total l) :
    ∀ i, normalized l i ≤ 2 * μ i := by
  have hpos : 0 < total l := by linarith
  intro i
  apply (div_le_iff₀ hpos).mpr
  have hh := mul_nonneg (hμ i) (show 0 ≤ 2 * total l - 1 by linarith)
  nlinarith only [hh, hle i]

/-- Every finite event loses at most the discarded mass after normalization. -/
theorem normalized_event_lower {μ l : ι → ℝ} {ε : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hle : ∀ i, l i ≤ μ i) (hμ₁ : total μ = 1)
    (hε : ε ≤ 1 / 2) (hL : 1 - ε ≤ total l) (E : Finset ι) :
    (∑ i ∈ E, μ i) - ε ≤ ∑ i ∈ E, normalized l i := by
  have hpos : 0 < total l := by linarith
  have hL₁ : total l ≤ 1 := by simpa [hμ₁] using total_mono hle
  have herr : (∑ i ∈ E, (μ i - l i)) ≤ 1 - total l := by
    calc
      _ ≤ ∑ i, (μ i - l i) :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => sub_nonneg.mpr (hle i))
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        change total μ - total l = 1 - total l
        rw [hμ₁]
  have hgain : (∑ i ∈ E, l i) ≤ ∑ i ∈ E, normalized l i := by
    apply Finset.sum_le_sum
    intro i _
    apply (le_div_iff₀ hpos).mpr
    simpa using mul_le_mul_of_nonneg_left hL₁ (hl i)
  rw [Finset.sum_sub_distrib] at herr
  linarith

end UniformSparsestCut.FiniteWeights

end OAI
