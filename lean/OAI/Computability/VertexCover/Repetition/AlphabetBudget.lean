import Mathlib
import OAI.Computability.VertexCover.Repetition.Scalar
import OAI.Computability.VertexCover.Repetition.SelectedMarginal

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

theorem selectedLabels_card (selected : Finset (Fin n)) :
    Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) =
      (Fintype.card A₁ * Fintype.card A₂) ^ selected.card := by
  simp [SelectedLabels, Fintype.card_prod, mul_pow]

theorem unusedCoordinates_card (selected : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ selected} = n - selected.card := by
  classical
  simp

theorem unusedCoordinates_card_real (selected : Finset (Fin n)) :
    (Fintype.card {i : Fin n // i ∉ selected} : ℝ) = (n : ℝ) - selected.card := by
  have hs : selected.card ≤ n := by simpa using Finset.card_le_univ selected
  rw [unusedCoordinates_card, Nat.cast_sub hs]

theorem log_le_logTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logTwo x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 ; norm_num
  unfold logTwo
  apply (le_div_iff₀ htwo).2
  simpa using mul_le_mul_of_nonneg_left htwo_le hlog

theorem selectedLabels_log_le [Nonempty A₁] [Nonempty A₂]
    (selected : Finset (Fin n)) (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) ≤
      (selected.card : ℝ) * ell := by
  have ha : (1 : ℝ) ≤ Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (1 : ℝ) ≤ Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hab : (1 : ℝ) ≤ (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) := by nlinarith
  rw [selectedLabels_card, Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((log_le_logTwo hab).trans hell) (Nat.cast_nonneg _)

omit [DecidableEq Q₁] [DecidableEq Q₂] in

theorem selectedInformationRadius_le [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    selectedInformationRadius G strategy selected ≤
      Real.sqrt (((n : ℝ) - selected.card) *
        ((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected))) := by
  have hprob : 1 ≤ 1 / G.selectedSuccess strategy selected := by
    apply (le_div_iff₀ positive).2
    simpa using G.selectedSuccess_le_one strategy selected
  have hbudget := add_le_add (selectedLabels_log_le (A₁ := A₁) (A₂ := A₂) selected ell hell)
    (log_le_logTwo hprob)
  unfold selectedInformationRadius
  rw [← unusedCoordinates_card_real selected]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)

theorem sqrt_budget_factor (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a * b) = a * Real.sqrt (b / a) := by
  have he : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]

omit [DecidableEq Q₁] [DecidableEq Q₂] in

theorem exists_coordinate_le_information_budget [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell)
    (hselected : selected.card < n)
    (error : {i : Fin n // i ∉ selected} → ℝ)
    (hsum : (∑ j, error j) ≤ 15 * selectedInformationRadius G strategy selected) :
    ∃ j : {i : Fin n // i ∉ selected}, error j ≤ 15 * Real.sqrt
      (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
        ((n : ℝ) - selected.card)) := by
  classical
  have hcard : 0 < Fintype.card {i : Fin n // i ∉ selected} := by
    rw [unusedCoordinates_card]
    exact Nat.sub_pos_of_lt hselected
  let : Nonempty {i : Fin n // i ∉ selected} := Fintype.card_pos_iff.mp hcard
  have hden : 0 < (n : ℝ) - selected.card := by
    rw [← unusedCoordinates_card_real selected]
    exact_mod_cast hcard
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left
    (selectedInformationRadius_le G strategy selected positive ell hell) (by norm_num : (0 : ℝ) ≤ 15))
  rw [sqrt_budget_factor _ _ hden] at htotal
  have havg : (∑ j, error j) ≤ ∑ _j : {i : Fin n // i ∉ selected},
      15 * Real.sqrt
        (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
          ((n : ℝ) - selected.card)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      unusedCoordinates_card_real, mul_assoc, mul_left_comm] using htotal
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨j, hj⟩

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
