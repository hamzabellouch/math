import OAI.NumberTheory.Ostmann.Preliminaries.ShiftedSieve
import OAI.NumberTheory.Ostmann.Preliminaries.SizeAssembly
import OAI.NumberTheory.Ostmann.Preliminaries.UniformWindowStability

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Filter
open scoped BigOperators

theorem summand_sqrt_bounds (d : Decomposition) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.A X ∧
      c * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.B X ∧
      (countUpTo d.A X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2 ∧
      (countUpTo d.B X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2 := by
  obtain ⟨CA, hCA, hA⟩ := eventually_countA_log_power d 3 (by decide)
  obtain ⟨CB, hCB, hB⟩ := eventually_countB_log_power d 3 (by decide)
  exact sqrt_bounds_of_cubic_log_sparsity d hCA hCB hA hB

theorem summand_polylog_lower (d : Decomposition) (j : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * Real.log (X : ℝ) ^ j ≤ countUpTo d.A X := by
  obtain ⟨C, hC, hB⟩ := eventually_countB_log_power d (j + 1) (by omega)
  exact ⟨Real.log 2 / (2 * C), by positivity,
    eventual_polylog_lower_of_upper d j hC hB⟩

theorem eventually_upperWindow_collision (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, (upperWindow d.A X).Nonempty ∧ (upperWindow d.B X).Nonempty ∧
      upperWindowCollision d X ≤ collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
  obtain ⟨c, C, hc, hC, hsize⟩ := summand_sqrt_bounds d
  exact upperWindow_collision_of_size_bounds d hc hC hsize

theorem eventually_upperWindow_mass_cap (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, (upperWindow d.A X).Nonempty ∧ (upperWindow d.B X).Nonempty ∧
      (∀ i : upperWindow d.A X, uniformWindowMass d.A X i ≤ collisionMassCap 4 X) ∧
      (∀ i : upperWindow d.B X, uniformWindowMass d.B X i ≤ collisionMassCap 4 X) := by
  obtain ⟨c, C, hc, hC, hsize⟩ := summand_sqrt_bounds d
  have hAcard := eventually_upperWindow_card_lower d.A hc hC
    (hsize.mono (fun X h => h.1)) (hsize.mono (fun X h => h.2.2.1))
  have hBcard := eventually_upperWindow_card_lower d.B hc hC
    (hsize.mono (fun X h => h.2.1)) (hsize.mono (fun X h => h.2.2.2))
  have hA := eventually_uniformWindowMass_cap d.A (show 0 < c / 2 by positivity) hAcard
  have hB := eventually_uniformWindowMass_cap d.B (show 0 < c / 2 by positivity) hBcard
  filter_upwards [hA, hB] with X hA hB
  exact ⟨hA.1, hB.1, hA.2, hB.2⟩

end Ostmann.Preliminaries

end OAI
