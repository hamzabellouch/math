import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace Balanced.WitnessDetection
noncomputable section
attribute [local instance] Classical.propDecidable

theorem detection_sum_ge_witness_card {D C : Type*} [Fintype D] [Fintype C]
    (forbidden : D → C → Prop) (h : D → C → ℝ) (a : ℝ)
    (hnonneg : ∀ d c, 0 ≤ h d c)
    (hdetect : ∀ d c, forbidden d c → a ≤ h d c) :
    a * ((Finset.univ.filter fun d => ∃ c, forbidden d c).card : ℝ) ≤
      ∑ d, ∑ c, h d c := by
  classical
  let W : Finset D := Finset.univ.filter fun d => ∃ c, forbidden d c
  calc
    a * (W.card : ℝ) = ∑ _d ∈ W, a := by simp [mul_comm]
    _ ≤ ∑ d ∈ W, ∑ c, h d c := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨c, hc⟩ := (Finset.mem_filter.mp hd).2
      exact (hdetect d c hc).trans (Finset.single_le_sum
        (fun c _ => hnonneg d c) (Finset.mem_univ c))
    _ ≤ ∑ d, ∑ c, h d c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W)
      intro d _ _
      exact Finset.sum_nonneg (fun c _ => hnonneg d c)

theorem uniform_witness_probability_le {D C : Type*} [Fintype D] [Fintype C]
    [Nonempty D] [Nonempty C]
    (forbidden : D → C → Prop) (h : D → C → ℝ) (a T : ℝ)
    (ha : 0 < a) (hnonneg : ∀ d c, 0 ≤ h d c)
    (hdetect : ∀ d c, forbidden d c → a ≤ h d c)
    (haverage : (∑ d, ∑ c, h d c) /
      ((Fintype.card D : ℝ) * Fintype.card C) ≤ T) :
    ((Finset.univ.filter fun d => ∃ c, forbidden d c).card : ℝ) /
      Fintype.card D ≤ (Fintype.card C : ℝ) * T / a := by
  classical
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hsum := detection_sum_ge_witness_card forbidden h a hnonneg hdetect
  have hav := (div_le_iff₀ (mul_pos hD hC)).mp haverage
  apply (le_div_iff₀ ha).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hD).mpr
  nlinarith

end
end Balanced.WitnessDetection

end OAI
