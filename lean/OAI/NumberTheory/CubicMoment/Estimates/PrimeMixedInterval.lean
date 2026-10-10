import OAI.NumberTheory.CubicMoment.Estimates.PrimeNormEndpoints

namespace OAI

/-! Intersections of the half-open norm restrictions arising from the
crossing test differ from the prime interval convention only at their
two final endpoints. -/
noncomputable section
namespace CubicFirstMoment

lemma mixed_norm_interval_away {a l b h x : ℝ}
    (hlo : x ≠ max a l) (hhi : x ≠ min b h) :
    (a < x ∧ l ≤ x ∧ x < b ∧ x ≤ h) ↔ max a l < x ∧ x ≤ min b h := by
  constructor
  · rintro ⟨ha,hl,hb,hh⟩
    refine ⟨?_,le_min hb.le hh⟩
    have hmx : max a l ≤ x := max_le ha.le hl
    exact lt_of_le_of_ne hmx hlo.symm
  · rintro ⟨hl,hh⟩
    have ha : a < x := (le_max_left _ _).trans_lt hl
    have hle : l ≤ x := ((le_max_right _ _).trans_lt hl).le
    have hb : x ≤ b := hh.trans (min_le_left _ _)
    have hstrict : x < b := by
      by_contra hn
      have hxb : x = b := le_antisymm hb (le_of_not_gt hn)
      have hxh : x ≤ h := hh.trans (min_le_right _ _)
      have hmin : min b h = x := by rw [←hxb,min_eq_left hxh]
      exact hhi hmin.symm
    exact ⟨ha,hle,hstrict,hh.trans (min_le_right _ _)⟩

end CubicFirstMoment

end

end OAI
