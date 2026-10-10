import OAI.Combinatorics.EditApproximation.Geometry.InputViews
import Mathlib.Logic.Equiv.Nat
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Integer word labels are encoded injectively using a sign bit. The
encoding preserves the actual unit-cost edit distance and takes one
linear pass; no constant-alphabet hypothesis is used. -/

namespace EditApproximation



theorem integerSymbolCode_eq (z : ℤ) : integerSymbolCode z = Equiv.intEquivNat z := by
  cases z <;> rfl

theorem integerSymbolCode_injective : Function.Injective integerSymbolCode := by
  intro x y heq
  apply Equiv.intEquivNat.injective
  simpa only [integerSymbolCode_eq] using heq

theorem integerSymbolCode_bound (z : ℤ) : integerSymbolCode z ≤ 2 * z.natAbs := by
  cases z <;> simp only [integerSymbolCode, Int.natAbs] <;> omega

theorem integerSymbolCode_bits (bound bits : ℕ) (hcapacity : 2 * (bound + 1) ≤ 2 ^ bits)
    (z : ℤ) (hz : z.natAbs ≤ bound) : integerSymbolCode z < 2 ^ bits := by
  have hcode := integerSymbolCode_bound z
  omega

theorem integerSymbols_edit (source target : List ℤ) :
    EditDistortion.edit (source.map integerSymbolCode) (target.map integerSymbolCode) =
      EditDistortion.edit source target := by
  apply EditDistortion.cost_map_eq_of_leftInverse integerSymbolCode Equiv.intEquivNat.symm
  intro z
  rw [integerSymbolCode_eq]
  exact Equiv.intEquivNat.symm_apply_apply z

theorem integerSymbols_equal_iff (source target : List ℤ) :
    source.map integerSymbolCode = target.map integerSymbolCode ↔ source = target :=
  ⟨fun h => (List.map_injective_iff.mpr integerSymbolCode_injective) h,
    fun h => congrArg (List.map integerSymbolCode) h⟩



theorem encodeIntegerSymbolsWithWork_spec (symbols : List ℤ) :
    encodeIntegerSymbolsWithWork symbols = (symbols.map integerSymbolCode, 3 * symbols.length) := by
  induction symbols with
  | nil => rfl
  | cons z zs ih =>
    simp only [encodeIntegerSymbolsWithWork, ih, List.map_cons, List.length_cons]
    congr 1

end EditApproximation

end OAI
