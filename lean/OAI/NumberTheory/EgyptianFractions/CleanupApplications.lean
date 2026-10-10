import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.RemoveRepetitions

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Existence follows from cleaning up the representation with `a` copies of `1/b`. -/
theorem egyptian_expansion_length_numerator (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∃ n : Fin a → ℕ, IsEgyptianExpansion ((a : ℚ) / b) n := by
  have hb : 0 < (b : ℚ) := by exact_mod_cast (show 0 < b by omega)
  have hx : (a : ℚ) / b < 1 := (div_lt_one hb).2 (by exact_mod_cast hab)
  exact remove_repetitions_below_one ((a : ℚ) / b) hx (fun _ => b)
    (fun _ => by omega) (by simp [div_eq_mul_inv])

/-- The set whose infimum defines the Egyptian length is nonempty. -/
theorem egyptianLengths_nonempty_cleanup (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (egyptianLengths a b).Nonempty :=
  ⟨a, egyptian_expansion_length_numerator a b ha hab⟩

/-- List-form interface for the dense-family and quantitative-tail constructions. -/
theorem egyptian_expansion_of_list (x : ℚ) (hx : x < 1) (l : List ℕ)
    (hpos : ∀ d ∈ l, 1 ≤ d)
    (hsum : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = x) :
    ∃ n : Fin l.length → ℕ, IsEgyptianExpansion x n := by
  apply remove_repetitions_below_one x hx l.get
  · intro i
    exact hpos _ (l.get_mem i)
  · have h := hsum
    rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn] at h
    exact h

end Problem337

end

end OAI
