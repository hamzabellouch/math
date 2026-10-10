import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Geometry.Parameters
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The two numerical constants used by online optimization are built from
the binary small-log parameter. Their word widths and construction costs
come from the actual multiplication loops. -/

namespace EditApproximation
namespace BinaryFraction



theorem onlineParametersWithWork_eta (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (onlineParametersWithWork ell hell).1.1.value = (rationalParameters (bitWordValue ell)).eta := by
  simp [onlineParametersWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue, rationalParameters]

theorem onlineParametersWithWork_kappa (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (onlineParametersWithWork ell hell).1.2.value = (rationalParameters (bitWordValue ell)).kappa := by
  simp [onlineParametersWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue, rationalParameters]

theorem onlineParametersWithWork_width (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) :
    (onlineParametersWithWork ell hell).1.1.width ≤ 5 * B + 1 ∧
      (onlineParametersWithWork ell hell).1.2.width ≤ 4 * B + 1 := by
  have he := bitPowerWithWork_length_le ell 5 B hB
  have hk := bitPowerWithWork_length_le ell 4 B hB
  simp only [onlineParametersWithWork, width, List.length_cons, List.length_nil]
  constructor <;> omega

theorem onlineParametersWithWork_cost (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) :
    (onlineParametersWithWork ell hell).2 ≤ bitPowerBitBudget 5 B + bitPowerBitBudget 4 B + 2 :=
  Nat.add_le_add_right
    (Nat.add_le_add (bitPowerWithWork_cost ell 5 B hB) (bitPowerWithWork_cost ell 4 B hB)) 2

theorem onlineParametersWithWork_range (ell : List Bool) (hell : 0 < bitWordValue ell)
    (H : ℕ) (hH : bitWordValue ell ≤ H) :
    |(onlineParametersWithWork ell hell).1.1.value| ≤ ((H ^ 5 : ℕ) : ℚ) ∧
      0 ≤ (onlineParametersWithWork ell hell).1.2.value ∧
      (onlineParametersWithWork ell hell).1.2.value ≤ 1 := by
  rw [onlineParametersWithWork_eta, onlineParametersWithWork_kappa]
  simp only [rationalParameters]
  have hn : (0 : ℚ) ≤ bitWordValue ell := Nat.cast_nonneg _
  have hp : (1 : ℚ) ≤ bitWordValue ell := by exact_mod_cast hell
  constructor
  · rw [abs_of_nonneg (pow_nonneg hn _), Nat.cast_pow]
    exact pow_le_pow_left₀ hn (by exact_mod_cast hH) _
  constructor
  · exact div_nonneg (by norm_num) (pow_nonneg hn _)
  · exact (div_le_one (pow_pos (lt_of_lt_of_le (by norm_num) hp) _)).mpr
      (one_le_pow₀ hp)

end BinaryFraction
end EditApproximation

end OAI
