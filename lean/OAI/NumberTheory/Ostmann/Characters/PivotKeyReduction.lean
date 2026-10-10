import OAI.NumberTheory.Ostmann.Construction.OriginalPivotTransfer

namespace OAI

/-! # Reduction of the actual integer pivot key at each constituent prime -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivotResidueKey_val (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ) :
    ((pivotResidueKey M L v).val : ZMod M) = (v : ZMod M) * (L : ZMod M)⁻¹ := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
    change (((v : ZMod (M + 1)) * (L : ZMod (M + 1))⁻¹).val : ZMod (M + 1)) = _
    exact ZMod.natCast_zmod_val _

/-- Key multiplication is valid already modulo the complete composite pivot. -/
theorem pivotResidueKey_mul (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ)
    (hL : L.Coprime M) :
    ((pivotResidueKey M L v).val : ZMod M) * (L : ZMod M) = (v : ZMod M) := by
  rw [pivotResidueKey_val, mul_assoc,
    ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime L M).mpr hL), mul_one]

/-- The same key reduces correctly at every prime dividing the pivot. No
field structure on the composite pivot ring is used. -/
theorem pivotResidueKey_mul_at_divisor (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ)
    {p : ℕ} (hp : p ∣ M) (hL : L.Coprime M) :
    ((pivotResidueKey M L v).val : ZMod p) * (L : ZMod p) = (v : ZMod p) := by
  have he := congrArg (ZMod.castHom hp (ZMod p)) (pivotResidueKey_mul M L v hL)
  simpa only [map_mul, map_natCast, map_intCast] using he

theorem positiveIntegerPivotKey_mul_at_divisor (M : ℕ) (hM : 0 < M)
    (L : ℕ) (v : ℤ) {p : ℕ} (hp : p ∣ M) (hL : L.Coprime M) :
    ((positiveIntegerPivotKey M hM L v).val : ZMod p) * (L : ZMod p) = (v : ZMod p) := by
  let : NeZero M := ⟨hM.ne'⟩
  exact pivotResidueKey_mul_at_divisor M L v hp hL

end Ostmann

end OAI
