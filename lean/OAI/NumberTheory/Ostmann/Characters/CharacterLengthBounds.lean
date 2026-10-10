import OAI.NumberTheory.Ostmann.Construction.InitialGapRate

namespace OAI

/-! # Uniform rounded character lengths -/
namespace Ostmann
open Filter

theorem eventual_character_length_bounds (z : ℝ) (hz : 1 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      L ≤ (⌊z * L⌋₊ : ℝ) ∧ (⌊z * L⌋₊ : ℝ) ≤ z * L ∧
      z * L ≤ 2 * (⌊z * L⌋₊ : ℝ) := by
  filter_upwards [eventually_bulkCount_bounds z (by linarith),
    eventually_ge_atTop (1 / (z - 1))] with L hbounds hL
  refine ⟨hbounds.1, hbounds.2.1, ?_, hbounds.2.2.1, hbounds.2.2.2⟩
  have hz0 : 0 < z - 1 := by linarith
  have hh := (div_le_iff₀ hz0).mp hL
  have hf := Nat.lt_floor_add_one (z * L)
  nlinarith only [hh, hf]

theorem eventual_character_length_ge (z C : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, C ≤ (⌊z * L⌋₊ : ℝ) := by
  exact eventually_bulkCount z hz _
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop C))

end Ostmann

end OAI
