import OAI.Combinatorics.BinaryEdit.CodeNumerics
import OAI.Combinatorics.BinaryEdit.EditDeficit
import OAI.Combinatorics.BinaryEdit.EncodingUpper

namespace OAI

/-! The exact arithmetic and metric estimates for fixed-length binary conversion. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- The precise 402 deficit estimate implies the required 804 ordinary-edit
estimate for a fixed pair of original words. Both metrics are the actual
unrestricted unit-cost edit distance. -/
theorem encode_bounds_of_deficit {α : Type u} {β : Type v} {M P : ℕ}
    (c : α → Word β P) {x y : List α}
    (hx : x.length = M) (hy : y.length = M)
    (hdef : (P : ℝ) / 402 * (deficit M x y : ℝ) ≤
      (deficit (M * P) (encode c x) (encode c y) : ℝ)) :
    (P : ℝ) / 804 * (ed x y : ℝ) ≤
        (ed (encode c x) (encode c y) : ℝ) ∧
      (ed (encode c x) (encode c y) : ℝ) ≤
        (P : ℝ) * (ed x y : ℝ) := by
  have hencx : (encode c x).length = M * P := by rw [length_encode, hx]
  have hency : (encode c y).length = M * P := by rw [length_encode, hy]
  have hsource := editDistance_deficit_bounds_real hx hy
  have htarget := editDistance_deficit_bounds_real hencx hency
  exact ⟨edit_lower_from_deficit (Nat.cast_nonneg P) hdef htarget.1 hsource.2,
    encode_editDistance_le_real c x y⟩

/-- A code satisfying the additive block-pair estimate, with short-pair error
at most half a block, has both advertised inequalities and the stronger
one-sided-deficit inequality. The zero-deficit case is included. -/
theorem encode_bounds_of_additive {α : Type u} {β : Type v}
    {M P error : ℕ} (c : α → Word β P) {x y : List α}
    (hx : x.length = M) (hy : y.length = M)
    (hadd : P * deficit M x y ≤
      201 * deficit (M * P) (encode c x) (encode c y) + error)
    (herr : 2 * error ≤ P) :
    ((P : ℝ) / 804 * (ed x y : ℝ) ≤
        (ed (encode c x) (encode c y) : ℝ) ∧
      (ed (encode c x) (encode c y) : ℝ) ≤
        (P : ℝ) * (ed x y : ℝ)) ∧
    (P : ℝ) / 402 * (deficit M x y : ℝ) ≤
      (deficit (M * P) (encode c x) (encode c y) : ℝ) := by
  have hdef := real_deficit_of_natural (natural_deficit_from_additive hadd herr)
  exact ⟨encode_bounds_of_deficit c hx hy hdef, hdef⟩

/-- The source's real-valued short-pair threshold gives its integer loss
budget without rounding changes. -/
theorem natural_short_pair_error {M : ℕ}
    (h : 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2) :
    2 * (2 * M * segmentThreshold M) ≤ M ^ 2 := by
  have h' : (2 : ℝ) * (2 * (M : ℝ) * segmentThreshold M) ≤ (M : ℝ) ^ 2 := by
    linarith
  exact_mod_cast h'

end TreeEdit.BinaryLower.Code

end OAI
