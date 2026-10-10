import OAI.Combinatorics.Crossing.FiniteSeparation
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace Zarankiewicz

theorem finite_scaled_radius {ι : Type*} [Fintype ι] (a r : ι → ℝ) (hr : ∀ i, 0<r i) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, |t|<δ → ∀ i, |a i*t|<r i := by
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ
    (fun i => r i/(|a i|+1)) (fun i _ => div_pos (hr i) (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro t ht i
  have hd : 0 < |a i|+1 := by positivity
  have hb : δ*(|a i|+1)<r i := (lt_div_iff₀ hd).mp (hbound i (Finset.mem_univ _))
  calc
    |a i*t| = |t| *|a i| := by rw [abs_mul,mul_comm]
    _ ≤ |t| *(|a i|+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    _ < δ*(|a i|+1) := mul_lt_mul_of_pos_right ht hd
    _ < r i := hb

end Zarankiewicz

end OAI
