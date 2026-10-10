import OAI.Combinatorics.Ryser.Incidence.DenseNeighborhood
import OAI.Combinatorics.Ryser.Incidence.WalkTrimming
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem exists_many_fourWalks
    (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (hG : G ⊆ A ×ˢ B) {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hA : (A.card : ℝ) ≤ V * n) (hB : (B.card : ℝ) ≤ V * n)
    (hE : n ^ 2 / V ≤ (G.card : ℝ)) :
    ∃ S : Finset α, S ⊆ A ∧
      3 * n / (8 * V ^ 2) ≤ (S.card : ℝ) ∧
      ∀ a ∈ S, ∀ a' ∈ S,
        n ^ 3 / (2 ^ 20 * V ^ 18) ≤ ((fourWalks A B G a a').card : ℝ) := by
  classical
  have hVpos : 0 < V := by linarith
  have hVne : V ≠ 0 := ne_of_gt hVpos
  obtain ⟨b, _hb, hsize, hbad⟩ :=
    exists_dense_neighborhood A B G hG hn hV hA hB hE
  have hc : 0 < n / (2 * V ^ 2) := by positivity
  have hm : 0 < ((neighbors A G b).card : ℝ) := hc.trans_le hsize
  have ht : 0 ≤ n / (512 * V ^ 8) := by positivity
  obtain ⟨S, hSsub, hScard, hwalks⟩ :=
    exists_trimmed_many_fourWalks (neighbors A G b) A B G
      (neighbors_subset A G b) (n / (512 * V ^ 8)) ht hm hbad
  refine ⟨S, hSsub.trans (neighbors_subset A G b), ?_, ?_⟩
  · calc
      3 * n / (8 * V ^ 2) = 3 * (n / (2 * V ^ 2)) / 4 := by
        field_simp [hVne]; ring
      _ ≤ 3 * ((neighbors A G b).card : ℝ) / 4 := by linarith
      _ ≤ (S.card : ℝ) := hScard
  · intro a ha a' ha'
    calc
      n ^ 3 / (2 ^ 20 * V ^ 18) =
          (n / (2 * V ^ 2)) / 2 * (n / (512 * V ^ 8)) ^ 2 := by
        field_simp [hVne]; ring
      _ ≤ ((neighbors A G b).card : ℝ) / 2 * (n / (512 * V ^ 8)) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ ((fourWalks A B G a a').card : ℝ) := hwalks a ha a' ha'

end RyserCoveringCounterexample.Incidence

end OAI
