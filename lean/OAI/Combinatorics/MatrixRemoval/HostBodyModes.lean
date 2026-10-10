import OAI.Combinatorics.MatrixRemoval.CanonicalHorizontal
import OAI.Combinatorics.MatrixRemoval.HostVerticalLocalization

namespace OAI

/-!
# Exhaustive localization of bodies in canonical host modes

All entry and role hypotheses refer to the actual canonical host. The numerical
order premise is exactly the four parent comparisons supplied by the two tree
orders.
-/
namespace Problem348.Construction
open ModeLocalization

/-- The necessary parent comparison for an ordered body in each of the six modes. -/
def BodyNodeOrder {h : ℕ} (t : Mode h) (r₀ r₁ c₀ c₁ : Position h) : Prop :=
  if kind t = 0 then positionNode r₀ / 2 ≤ positionNode r₁
  else if kind t = 1 then positionNode r₀ ≤ positionNode r₁ / 2
  else if kind t < 4 then positionNode c₀ ≤ positionNode c₁ / 2
  else positionNode c₀ / 2 ≤ positionNode c₁

theorem rowRole_first_variable {h : ℕ} {t : Mode h} {x : Position h}
    (hx : rowRole t 0 x) : ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [rowRole] at hx
  · exact ⟨v, rfl⟩
  · simp [rowRole] at hx

theorem colRole_horizontal_variable {h : ℕ} {t : Mode h} {j : Fin 2}
    {x : Position h} (hk : 2 ≤ kind t) (hx : colRole t j x) :
    ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [colRole] at hx
  · exact ⟨v, rfl⟩
  · simp [colRole] at hx
    omega

/-- The horizontal plus roles cannot realize the body's top row. -/
theorem host_horizontal_plus_not_body {h : ℕ} {t : Mode h}
    (hklo : 2 ≤ kind t) (hkhi : kind t < 4) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode c₀ ≤ positionNode c₁ / 2) :
    ¬ IsP (host r₀ c₀) (host r₀ c₁) (host r₁ c₀) (host r₁ c₁) := by
  obtain ⟨r, rfl⟩ := rowRole_first_variable hr₀
  obtain ⟨c, rfl⟩ := colRole_horizontal_variable hklo hc₀
  obtain ⟨d, rfl⟩ := colRole_horizontal_variable hklo hc₁
  have hk0 : kind t ≠ 0 := by omega
  have hk1 : kind t ≠ 1 := by omega
  have hk2 : ¬ kind t < 2 := by omega
  have hr : AtLevel (level t) true r ∧ node r % 2 = kind t % 2 := by
    simpa [rowRole, hk0, hk1, hkhi] using hr₀
  have hc : AtLevel (level t - 1) true c := by
    simpa [colRole, hk2, hkhi] using hc₀
  have hd : AtLevel (level t) true d ∧ node d % 2 = kind t % 2 := by
    simpa [colRole, hk2, hkhi] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  intro hb
  exact horizontal_plus_entries_impossible (hl ▸ hr.1) hc (hl ▸ hd.1)
    horder (hr.2.trans hd.2.symm) hb.1 hb.2.1

/-- The horizontal minus roles force the body's top-left entry onto a shared leaf. -/
theorem host_horizontal_minus_leaf_diagonal {h : ℕ} {t : Mode h}
    (hklo : 4 ≤ kind t) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode c₀ / 2 ≤ positionNode c₁)
    (hb : IsP (host r₀ c₀) (host r₀ c₁) (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) := by
  obtain ⟨r, rfl⟩ := rowRole_first_variable hr₀
  obtain ⟨c, rfl⟩ := colRole_horizontal_variable (by omega) hc₀
  obtain ⟨d, rfl⟩ := colRole_horizontal_variable (by omega) hc₁
  have hk0 : kind t ≠ 0 := by omega
  have hk1 : kind t ≠ 1 := by omega
  have hk2 : ¬ kind t < 2 := by omega
  have hk4 : ¬ kind t < 4 := by omega
  have hr : AtLevel (level t) false r ∧ node r % 2 = kind t % 2 := by
    simpa [rowRole, hk0, hk1, hk4] using hr₀
  have hc : AtLevel (level t) false c ∧ node c % 2 = kind t % 2 := by
    simpa [colRole, hk2, hk4] using hc₀
  have hd : AtLevel (level t - 1) false d := by
    simpa [colRole, hk2, hk4] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  obtain ⟨_, z, hz, hcz⟩ := horizontal_minus_entries_localize
    (hl ▸ hr.1) (hl ▸ hc.1) hd horder (hr.2.trans hc.2.symm) hb.1 hb.2.1
  exact ⟨z, congrArg (fun v => Sum.inr (Sum.inl v)) hz,
    congrArg (fun v => Sum.inr (Sum.inl v)) hcz⟩

/-- Under `BodyNodeOrder`, every ordered body in any canonical mode has its
top-left cell on the shared leaf diagonal. -/
theorem host_body_leaf_diagonal {h : ℕ} {t : Mode h} {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : BodyNodeOrder t r₀ r₁ c₀ c₁)
    (hb : IsP (host r₀ c₀) (host r₀ c₁) (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) := by
  by_cases hk0 : kind t = 0
  · exact False.elim (host_vertical_plus_not_body hk0 hr₀ hr₁ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0] using horder) hb)
  by_cases hk1 : kind t = 1
  · exact False.elim (host_vertical_minus_not_body hk1 hr₀ hr₁ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0, hk1] using horder) hb)
  by_cases hk4 : kind t < 4
  · exact False.elim (host_horizontal_plus_not_body (by omega) hk4 hr₀ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0, hk1, hk4] using horder) hb)
  · exact host_horizontal_minus_leaf_diagonal (by omega) hr₀ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0, hk1, hk4] using horder) hb

end Problem348.Construction

end OAI
