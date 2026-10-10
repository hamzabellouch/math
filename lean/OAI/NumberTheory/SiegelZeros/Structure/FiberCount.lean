import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import OAI.NumberTheory.SiegelZeros.Selection.SelectionBridge

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W31

theorem first_coordinate_fiber_card_le (P : Finset MultiIndex) (B : ℝ)
    (hb : ∀ a ∈ P, (a 1 : ℝ) ≤ B ∧ (a 2 : ℝ) ≤ B) (n : ℕ) :
    (P.filter (fun a => a 0 = n)).card ≤ (Nat.floor B + 1) ^ 2 := by
  classical
  have hcard : (P.filter (fun a => a 0 = n)).card ≤
      ((Finset.range (Nat.floor B + 1)) ×ˢ
        (Finset.range (Nat.floor B + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun a : MultiIndex => (a 1, a 2))
    · intro a ha
      have haP := (Finset.mem_filter.mp ha).1
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hb a haP).1))
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hb a haP).2))
    · intro a ha b hb' hab
      have h0 : a 0 = b 0 :=
        (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb').2.symm
      have h1 : a 1 = b 1 := congrArg Prod.fst hab
      have h2 : a 2 = b 2 := congrArg Prod.snd hab
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
  simpa [Finset.card_product, pow_two] using hcard

theorem cutoff_fiber_card_le {H U : ℝ} (hH : 0 < H) (P : Finset MultiIndex)
    (hcut : ∀ a ∈ P, weight H a ≤ 96 * H ^ (2 / 3 : ℝ) * U) (n : ℕ) :
    (P.filter (fun a => a 0 = n)).card ≤
      (Nat.floor (96 * H ^ (-(1 / 3 : ℝ)) * U) + 1) ^ 2 := by
  exact first_coordinate_fiber_card_le P _
    (fun a ha => short_coordinates_le hH a (hcut a ha)) n

end SiegelZerosAwei.W31


end SiegelZeros

end OAI
