import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem point_assignment_injective_of_few_merged
    {G X : Type*} [Fintype G] [DecidableEq G]
    {Label : G → Type*}
    (label : (g : G) → X → Label g)
    (joining : X → X → G)
    (mergedAt : X → Finset G)
    (few_merged : ∀ x, (mergedAt x).card + 1 < Fintype.card G)
    (cross_direction : ∀ x y, x ≠ y → ∀ g, g ≠ joining x y →
      label g x = label g y → g ∈ mergedAt x) :
    Function.Injective (fun x g => label g x) := by
  intro x y hlabels
  by_contra hxy
  have hsub : Finset.univ.erase (joining x y) ⊆ mergedAt x := by
    intro g hg
    exact cross_direction x y hxy g (Finset.mem_erase.mp hg).1
      (congrFun hlabels g)
  have hcard := Finset.card_le_card hsub
  have hsize : (Finset.univ.erase (joining x y)).card = Fintype.card G - 1 := by
    simp
  have hfew := few_merged x
  omega

theorem multiplicity_lt_order_of_size_condition
    {q B : ℕ} {ρ : ℝ}
    (hρ : ρ < 1) (hq : 0 ≤ (q : ℝ))
    (hsize : 2 * (1 + (B : ℝ)) < ρ * q) : B < q := by
  have hmul : ρ * (q : ℝ) ≤ q := mul_le_of_le_one_left hq (le_of_lt hρ)
  have hreal : (B : ℝ) < q := by linarith
  exact_mod_cast hreal

end Balanced

end OAI
