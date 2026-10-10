import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLineFamiliesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeLineFamilies
variable {ι : Type*} (p : ℕ) [Fact p.Prime]

def probability (a b : ι → ZMod p) : ℝ :=
  (Nat.card (Solutions a b) : ℝ) / Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ)

theorem probability_rank_one (a b : ι → ZMod p) (i : ι)
    (hai : a i ≠ 0) (hbi : b i ≠ 0) (hm : ∀ j, minor a b i j = 0) :
    probability p a b = ((p-1 : ℕ) : ℝ)⁻¹ := by
  rw [probability, card_rank_one a b i hai hbi hm, Fintype.card_prod, ZMod.card_units]
  have hp1 : 0 < p-1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  push_cast
  field_simp

theorem probability_all_zero (a b : ι → ZMod p) (hz : AllZero a b) :
    probability p a b = 1 := by
  rw [probability, card_all_zero a b hz]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem probability_rank_two (a b : ι → ZMod p) (i j : ι)
    (hij : minor a b i j ≠ 0) : probability p a b = 0 := by
  simp only [probability, card_rank_two a b i j hij, Nat.cast_zero, zero_div]

theorem probability_single_coefficient (a b : ι → ZMod p) (i : ι)
    (hi : (a i = 0 ∧ b i ≠ 0) ∨ (a i ≠ 0 ∧ b i = 0)) :
    probability p a b = 0 := by
  simp only [probability, card_single_coefficient a b i hi, Nat.cast_zero, zero_div]

theorem probability_eq_flags (a b : ι → ZMod p) :
    probability p a b = (by
      classical
      exact if AllZero a b then 1
        else if AllMinorsZero a b ∧ ∃ i, a i ≠ 0 ∧ b i ≠ 0
        then ((p-1 : ℕ) : ℝ)⁻¹ else 0) := by
  classical
  by_cases hz : AllZero a b
  · simp only [hz, ite_true]
    exact probability_all_zero p a b hz
  · simp only [hz, ite_false]
    by_cases hr : AllMinorsZero a b ∧ ∃ i, a i ≠ 0 ∧ b i ≠ 0
    · simp only [hr]
      obtain ⟨hm, i, hai, hbi⟩ := hr
      exact probability_rank_one p a b i hai hbi (hm i)
    · simp only [hr, ite_false]
      have : IsEmpty (Solutions a b) := ⟨fun z => by
        have h := (solutions_nonempty_iff a b).mp ⟨z⟩
        exact h.elim hz hr⟩
      simp only [probability, Nat.card_of_isEmpty, Nat.cast_zero, zero_div]

theorem probability_le_unit_line (a b : ι → ZMod p) (hz : ¬ AllZero a b) :
    probability p a b ≤ ((p-1 : ℕ) : ℝ)⁻¹ := by
  classical
  rw [probability_eq_flags]
  simp only [hz, ite_false]
  split_ifs
  · exact le_rfl
  · positivity

end Ostmann.Arithmetic.PrimeLineFamilies
end

end OAI
