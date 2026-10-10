import OAI.NumberTheory.Ostmann.Arithmetic.PrimeMixedLineFamiliesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeMixedLineFamilies
variable {ι : Type*} (p : ℕ) [Fact p.Prime]

def probability (a b : ι → ZMod p) : ℝ :=
  (Nat.card (Solutions a b):ℝ) / Fintype.card (ZMod p × (ZMod p)ˣ)

theorem probability_rank_one (a b : ι → ZMod p) (i : ι)
    (hai : a i≠0) (hm : ∀ j, minor a b i j=0) : probability p a b=(p:ℝ)⁻¹ := by
  rw [probability,card_rank_one a b i hai hm,Fintype.card_prod,ZMod.card,ZMod.card_units]
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hp1 : 0<p-1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  push_cast
  field_simp

theorem probability_all_zero (a b : ι → ZMod p) (hz : AllZero a b) : probability p a b=1 := by
  rw [probability,card_all_zero a b hz]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem probability_rank_two (a b : ι → ZMod p) (i j : ι)
    (hij : minor a b i j≠0) : probability p a b=0 := by
  simp only [probability,card_rank_two a b i j hij,Nat.cast_zero,zero_div]

theorem probability_zero_external_coefficient (a b : ι → ZMod p) (i : ι)
    (hai : a i=0) (hbi : b i≠0) : probability p a b=0 := by
  simp only [probability,card_zero_external_coefficient a b i hai hbi,Nat.cast_zero,zero_div]

theorem probability_eq_flags (a b : ι → ZMod p) :
    probability p a b = (by
      classical
      exact if AllZero a b then 1 else if AllMinorsZero a b ∧ ∃ i, a i≠0
        then (p:ℝ)⁻¹ else 0) := by
  classical
  by_cases hz : AllZero a b
  · simp only [hz,ite_true]
    exact probability_all_zero p a b hz
  · simp only [hz,ite_false]
    by_cases hr : AllMinorsZero a b ∧ ∃ i, a i≠0
    · simp only [hr]
      obtain ⟨hm,i,hai⟩ := hr
      exact probability_rank_one p a b i hai (hm i)
    · simp only [hr,ite_false]
      have : IsEmpty (Solutions a b) := ⟨fun z => by
        have hh := (solutions_nonempty_iff a b).mp ⟨z⟩
        exact hh.elim hz hr⟩
      simp only [probability,Nat.card_of_isEmpty,Nat.cast_zero,zero_div]

theorem probability_le_mixed_line (a b : ι → ZMod p) (hz : ¬ AllZero a b) :
    probability p a b ≤ (p:ℝ)⁻¹ := by
  classical
  rw [probability_eq_flags]
  simp only [hz,ite_false]
  split_ifs
  · exact le_rfl
  · positivity

theorem probability_le_unit_line (a b : ι → ZMod p) (hz : ¬ AllZero a b) :
    probability p a b ≤ ((p-1:ℕ):ℝ)⁻¹ := by
  apply (probability_le_mixed_line p a b hz).trans
  apply inv_anti₀
  · exact_mod_cast Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  · exact_mod_cast Nat.sub_le p 1

end Ostmann.Arithmetic.PrimeMixedLineFamilies

end

end OAI
