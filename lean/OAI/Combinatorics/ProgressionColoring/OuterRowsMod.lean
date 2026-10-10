import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.ModEq

namespace OAI

/-!
# Residue classes in a finite interval

Each residue class modulo `w` occurs at least `n / w` times in `Fin n`.
On any interval of length at most `w`, reduction modulo `w` is injective.
-/

namespace QuantitativeVanDerWaerden

/-- Each row modulo `w` contains at least one point from each complete block. -/
theorem card_mod_row_lower (n w : ℕ) (hw : 0 < w) (j : Fin w) :
    n / w ≤ (Finset.univ.filter (fun i : Fin n => i.val % w = j.val)).card := by
  let f : Fin (n / w) → Fin n := fun k =>
    ⟨k.val * w + j.val, by
      calc
        k.val * w + j.val < k.val * w + w := Nat.add_lt_add_left j.isLt _
        _ = (k.val + 1) * w := by simp [Nat.add_mul]
        _ ≤ (n / w) * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt k.isLt)
        _ ≤ n := Nat.div_mul_le_self n w⟩
  have hf : Function.Injective f := by
    intro k l h
    apply Fin.ext
    have hval : k.val * w + j.val = l.val * w + j.val := congrArg Fin.val h
    exact Nat.eq_of_mul_eq_mul_right hw (Nat.add_right_cancel hval)
  have hmem : ∀ k ∈ (Finset.univ : Finset (Fin (n / w))),
      f k ∈ Finset.univ.filter (fun i : Fin n => i.val % w = j.val) := by
    intro k _
    simp [f, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card_of_injOn f hmem (fun _ _ _ _ h => hf h)

/-- Subtype-cardinality form of `card_mod_row_lower`. -/
theorem card_mod_row_subtype_lower (n w : ℕ) (hw : 0 < w) (j : Fin w) :
    n / w ≤ Fintype.card {i : Fin n // i.val % w = j.val} := by
  simpa only [Fintype.card_subtype] using card_mod_row_lower n w hw j

/-- Equal residues in one interval of width `w` represent the same number. -/
theorem eq_of_mod_eq_of_mem_interval {a w x y : ℕ}
    (hxlo : a ≤ x) (hxhi : x < a + w)
    (hylo : a ≤ y) (hyhi : y < a + w)
    (hmod : x % w = y % w) : x = y := by
  have hxy : Nat.ModEq w x y := hmod
  exact Nat.le_antisymm (hxy.le_of_lt_add (by omega))
    (hxy.symm.le_of_lt_add (by omega))

/-- Cross multiplication gives a comparison of the integer row-size bounds. -/
theorem div_le_div_of_mul_le {M w d L : ℕ}
    (hw : 0 < w) (hd : 0 < d) (h : M * w ≤ d * L) :
    M / d ≤ L / w := by
  apply (Nat.le_div_iff_mul_le hw).mpr
  apply Nat.le_of_mul_le_mul_left (c := d) _ hd
  calc
    d * (M / d * w) = (M / d * d) * w := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ M * w := Nat.mul_le_mul_right w (Nat.div_mul_le_self M d)
    _ ≤ d * L := h

theorem div_ten_le_div_of_sandwich {M w k L : ℕ}
    (hw : 0 < w) (hlo : M * w ≤ k) (hhi : k ≤ 10 * L) :
    M / 10 ≤ L / w :=
  div_le_div_of_mul_le hw (by decide) (hlo.trans hhi)

end QuantitativeVanDerWaerden

end OAI
