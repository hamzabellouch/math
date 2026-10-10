import OAI.Combinatorics.EditApproximation.Geometry.HeightPowerWork

namespace OAI

namespace EditApproximation
open Filter

theorem integer_encoded_symbol_bits (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ a ∈ source.map integerSymbolCode ++ target.map integerSymbolCode,
        Nat.size a ≤ inputHeight N ^ 3 := by
  filter_upwards [inputHeight_real_tendsto.eventually
    (eventually_ge_atTop ((max 100 C : ℕ) : ℝ))] with N hH
  have hH' : max 100 C ≤ inputHeight N := by exact_mod_cast hH
  intro source target halphabet a ha
  rw [← List.map_append] at ha
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  have hcode : Nat.size (integerSymbolCode z) ≤ integerInputSymbolBits source target :=
    Nat.size_le.mpr (integerInputSymbolBits_fits source target z hz)
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hn := input_length_bits_le N
  have hCH := Nat.mul_le_mul (show C ≤ inputHeight N by omega) hn
  have hcube : 100 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
    have hm := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 100 ≤ inputHeight N by omega)
    nlinarith only [hm]
  have h100 : 100 ≤ inputHeight N := by omega
  nlinarith only [hcode, hs, hCH, hcube, h100]

end EditApproximation

end OAI
