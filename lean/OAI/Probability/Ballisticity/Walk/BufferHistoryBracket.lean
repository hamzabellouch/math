import Mathlib
import OAI.Probability.Ballisticity.Geometry.BufferElapsedHeight

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferWordHeight_length (l : List (ℕ × Bool)) : l.length ≤ bufferWordHeight l := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.length_cons,bufferWordHeight]; omega

lemma nat_increasing_bracket (b : ℕ → ℕ) (h0 : b 0=0) (h : ∀ n, b n < b (n+1)) (t : ℕ) :
    ∃ n, b n ≤ t ∧ t < b (n+1) := by
  have hbn : ∀ n, n ≤ b n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have hh := h n; omega
  have hex : ∃ n, t < b n := ⟨t+1,lt_of_lt_of_le (Nat.lt_succ_self t) (hbn (t+1))⟩
  let k := Nat.find hex
  have hk : t < b k := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra hn
    have he : k=0 := by omega
    rw [he,h0] at hk
    omega
  refine ⟨k-1,?_,?_⟩
  · have hh := Nat.find_min hex (show k-1<k by omega)
    exact le_of_not_gt hh
  · simpa only [Nat.sub_add_cancel hk0] using hk

lemma bufferHistory_bracket {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (t : ℕ) :
    ∃ n, let l := bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n
      bufferWordHeight l ≤ t ∧ t < bufferWordHeight
        (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω (n+1)) := by
  apply nat_increasing_bracket
  · rfl
  · intro n
    simp only [bufferHistory,bufferWordHeight]
    omega
end DirectionalTransience

end

end

end OAI
