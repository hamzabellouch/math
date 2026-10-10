import OAI.NumberTheory.Ostmann.Preliminaries.WindowMass

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Filter
open scoped BigOperators

noncomputable def upperWindowCollision (d : Decomposition) (X : ℕ) : ℝ :=
  collisionStability d (collisionScale 4 X)
    (fun i : upperWindow d.A X => i.val) (uniformWindowMass d.A X)
    (fun i : upperWindow d.B X => i.val) (uniformWindowMass d.B X)

theorem upperWindow_collision_of_size_bounds (d : Decomposition) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hsizes : ∀ᶠ X : ℕ in atTop,
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.A X ∧
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.B X ∧
      (countUpTo d.A X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2 ∧
      (countUpTo d.B X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2) :
    ∀ᶠ X : ℕ in atTop, (upperWindow d.A X).Nonempty ∧ (upperWindow d.B X).Nonempty ∧
      upperWindowCollision d X ≤ collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
  classical
  have hAcard := eventually_upperWindow_card_lower d.A hc hC
    (hsizes.mono (fun X h => h.1)) (hsizes.mono (fun X h => h.2.2.1))
  have hBcard := eventually_upperWindow_card_lower d.B hc hC
    (hsizes.mono (fun X h => h.2.1)) (hsizes.mono (fun X h => h.2.2.2))
  have hAcap := eventually_uniformWindowMass_cap d.A (show 0 < c / 2 by positivity) hAcard
  have hBcap := eventually_uniformWindowMass_cap d.B (show 0 < c / 2 by positivity) hBcard
  filter_upwards [hAcap, hBcap, eventually_upperWindow_large d.cutoff,
    eventually_collision_bound_conditions 4] with X hAcap hBcap hlarge hcond
  refine ⟨hAcap.1, hBcap.1, ?_⟩
  apply collisionStability_le_loglog d 4 X hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
    (fun i : upperWindow d.A X => i.val) (uniformWindowMass d.A X)
    (fun i : upperWindow d.B X => i.val) (uniformWindowMass d.B X)
    Subtype.val_injective Subtype.val_injective
  · exact fun i => (mem_upperWindow.mp i.property).2.1
  · exact fun i => (mem_upperWindow.mp i.property).2.1
  · exact uniformWindowMass_nonneg d.A X
  · exact uniformWindowMass_nonneg d.B X
  · exact uniformWindowMass_sum d.A X hAcap.1
  · exact uniformWindowMass_sum d.B X hBcap.1
  · exact fun i _ => (mem_upperWindow.mp i.property).1
  · exact fun i _ => (mem_upperWindow.mp i.property).1
  · exact fun i _ => hlarge.trans_le (mem_upperWindow.mp i.property).2.2
  · exact fun i _ => hlarge.trans_le (mem_upperWindow.mp i.property).2.2
  · exact hAcap.2
  · exact hBcap.2

end Ostmann.Preliminaries

end OAI
