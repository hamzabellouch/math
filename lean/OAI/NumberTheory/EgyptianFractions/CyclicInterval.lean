import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A point to the right of an inner interval is separated from that interval
in both directions around the cyclic group. -/
theorem cyclic_sub_val_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d : ℕ) (hy : d ≤ y.val)
    (hgap : y.val + d ≤ x.val) :
    d ≤ (x - y).val ∧ (x - y).val + d ≤ q := by
  have hxq := ZMod.val_lt x
  rw [ZMod.val_sub (by omega : y.val ≤ x.val)]
  omega

/-- Normalized version of the cyclic separation estimate. -/
theorem cyclic_sub_phase_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d : ℕ) (hy : d ≤ y.val)
    (hgap : y.val + d ≤ x.val) :
    (d : ℝ) / q ≤ ((x - y).val : ℝ) / q ∧
    ((x - y).val : ℝ) / q ≤ 1 - (d : ℝ) / q := by
  obtain ⟨hlo, hhi⟩ := cyclic_sub_val_margin x y d hy hgap
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  constructor
  · apply div_le_div_of_nonneg_right _ hq.le
    exact_mod_cast hlo
  · apply (div_le_iff₀ hq).mpr
    have hh : ((x - y).val : ℝ) + d ≤ q := by exact_mod_cast hhi
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hq)]
    linarith

/-- An inner initial interval with margin `d` lies away from every point
outside the initial target interval ending at `B+d`. -/
theorem cyclic_initial_interval_phase_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d B : ℕ)
    (hx : B + d ≤ x.val) (hy : d ≤ y.val ∧ y.val ≤ B) :
    (d : ℝ) / q ≤ ((x - y).val : ℝ) / q ∧
    ((x - y).val : ℝ) / q ≤ 1 - (d : ℝ) / q :=
  cyclic_sub_phase_margin x y d hy.1 (by omega)

/-- A cyclic interval is the image of its ordinary representatives. -/
theorem cyclic_interval_eq_image {q : ℕ} [NeZero q] (a b : ℕ) (hb : b < q) :
    (Finset.univ.filter (fun x : ZMod q => a ≤ x.val ∧ x.val ≤ b)) =
      (Finset.Icc a b).image (fun n : ℕ => (n : ZMod q)) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x.val, Finset.mem_Icc.mpr hx, ZMod.natCast_zmod_val x⟩
  · rintro ⟨n, hn, rfl⟩
    have hn' := Finset.mem_Icc.mp hn
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < q)] using hn'

/-- Exact cardinality of a cyclic interval which does not cross zero. -/
theorem cyclic_interval_card {q : ℕ} [NeZero q] (a b : ℕ) (hb : b < q) :
    (Finset.univ.filter (fun x : ZMod q => a ≤ x.val ∧ x.val ≤ b)).card =
      b + 1 - a := by
  classical
  rw [cyclic_interval_eq_image a b hb]
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod q)) (Finset.Icc a b) := by
    intro n hn m hm hnm
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    have h := congrArg ZMod.val hnm
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < q),
      Nat.mod_eq_of_lt (by omega : m < q)] using h
  rw [Finset.card_image_iff.mpr hinj, Nat.card_Icc]

end Problem337

end

end OAI
