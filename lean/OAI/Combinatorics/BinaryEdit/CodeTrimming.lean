import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.BinaryEdit.SubsequenceIntersection
import OAI.Combinatorics.BinaryEdit.LCS

namespace OAI

/-!
# The local span-trimming step in fixed-length binary conversion

If a matched subsequence occupies two larger contiguous spans, taking prefixes
of those spans deletes at most the total number of removed positions from the
matching. This lemma does not assume that matched positions are consecutive.
-/

namespace TreeEdit.BinaryLower.Code

universe u

/-- Trimming two words loses at most the sum of the numbers of removed symbols
from any fixed common subsequence. -/
theorem common_sublist_take {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y) (a b : ℕ) :
    ∃ w : List α, w.Sublist (x.take a) ∧ w.Sublist (y.take b) ∧
      z.length ≤ w.length + (x.length - a) + (y.length - b) := by
  obtain ⟨u, huz, hux, hu⟩ :=
    common_sublist_lower_bound hzx (List.take_sublist a x)
  obtain ⟨w, hwu, hwy, hw⟩ :=
    common_sublist_lower_bound (huz.trans hzy) (List.take_sublist b y)
  refine ⟨w, hwu.trans hux, hwy, ?_⟩
  simp only [List.length_take] at hu hw
  omega

/-- The manuscript trims each span to the number of matched symbols. -/
theorem common_sublist_trim_to_matched_length {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y) :
    ∃ w : List α, w.Sublist (x.take z.length) ∧ w.Sublist (y.take z.length) ∧
      z.length ≤ w.length + ((x.length - z.length) + (y.length - z.length)) := by
  obtain ⟨w, hwx, hwy, hlen⟩ := common_sublist_take hzx hzy z.length z.length
  exact ⟨w, hwx, hwy, by omega⟩

/-- A 99-percent separation bound on the two trimmed segments charges at least
one unmatched span position for each hundred matches. All arithmetic here is
in natural numbers, avoiding rounding or division conventions. -/
theorem trim_separation_charge {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y)
    (hsep : ∀ w : List α, w.Sublist (x.take z.length) →
      w.Sublist (y.take z.length) → 100 * w.length ≤ 99 * z.length) :
    z.length ≤ 100 * ((x.length - z.length) + (y.length - z.length)) := by
  obtain ⟨w, hwx, hwy, hlen⟩ := common_sublist_trim_to_matched_length hzx hzy
  have h := hsep w hwx hwy
  omega

/-- The trimming bound stated directly for the actual LCS maximum. -/
theorem lcs_take_loss_le {α : Type u} (x y : List α) (a b : ℕ) :
    lcs x y ≤ lcs (x.take a) (y.take b) + (x.length - a) + (y.length - b) := by
  obtain ⟨z, hzx, hzy, hz⟩ := exists_lcs x y
  obtain ⟨w, hwx, hwy, hw⟩ := common_sublist_take hzx hzy a b
  have hmax := length_le_lcs hwx hwy
  omega

/-- A version of the local charge which accepts the segment code's LCS
separation hypothesis directly. -/
theorem trim_separation_charge_lcs {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y)
    (hsep : 100 * lcs (x.take z.length) (y.take z.length) ≤ 99 * z.length) :
    z.length ≤ 100 * ((x.length - z.length) + (y.length - z.length)) := by
  apply trim_separation_charge hzx hzy
  intro w hwx hwy
  exact (Nat.mul_le_mul_left 100 (length_le_lcs hwx hwy)).trans hsep

/-- Real-valued form of the source's `g ≥ 0.01 a` charge. -/
theorem trim_separation_charge_real {α : Type u} {x y z : List α}
    (hzx : z.Sublist x) (hzy : z.Sublist y)
    (hsep : 100 * lcs (x.take z.length) (y.take z.length) ≤ 99 * z.length) :
    (z.length : ℝ) / 100 ≤
      ((x.length - z.length : ℕ) : ℝ) + ((y.length - z.length : ℕ) : ℝ) := by
  have h := trim_separation_charge_lcs hzx hzy hsep
  have hr : (z.length : ℝ) ≤
      100 * (((x.length - z.length : ℕ) : ℝ) + ((y.length - z.length : ℕ) : ℝ)) := by
    exact_mod_cast h
  linarith

end TreeEdit.BinaryLower.Code

end OAI
