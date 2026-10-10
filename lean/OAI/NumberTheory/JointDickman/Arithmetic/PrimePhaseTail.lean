import OAI.NumberTheory.JointDickman.Arithmetic.PrimePhaseDivergence

namespace OAI

/-! # Prime-phase separation after fixed prime deletions -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma prime_abs_cosine_deleted_cost (P : Finset ℕ) (X t : ℝ) :
    (∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
      (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
    (∑ p ∈ ((Icc 2 ⌊X⌋₊).filter Nat.Prime) \ P,
      (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ)) +
      ∑ p ∈ P, 1 / (p : ℝ) := by
  let S := (Icc 2 ⌊X⌋₊).filter Nat.Prime
  let v := fun p : ℕ => (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ)
  have he := sum_inter_add_sum_sdiff S P v
  have hi : (∑ p ∈ S ∩ P, v p) ≤ ∑ p ∈ P, 1 / (p : ℝ) := by
    calc
      _ ≤ ∑ p ∈ S ∩ P, 1 / (p : ℝ) := by
        apply sum_le_sum
        intro p _
        exact div_le_div_of_nonneg_right (by linarith [abs_nonneg (Real.cos (t * Real.log (p : ℝ) / 2))])
          (Nat.cast_nonneg p)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right
        (fun p _ _ => by positivity)
  change (∑ p ∈ S, v p) ≤ (∑ p ∈ S \ P, v p) + _
  linarith

theorem prime_abs_cosine_deleted_diverges (P : Finset ℕ) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ 2*X →
      R ≤ ∑ p ∈ ((Icc 2 ⌊X⌋₊).filter Nat.Prime) \ P,
        (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ) := by
  filter_upwards [prime_abs_cosine_defect_diverges (R + ∑ p ∈ P, 1 / (p : ℝ))] with X hX
  intro t htlo ht
  have hl := hX t htlo ht
  have hh := prime_abs_cosine_deleted_cost P X t
  linarith

end JointDickman

end OAI
