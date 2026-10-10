import OAI.Analysis.GroupDeterminants.LampCoefficients

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft GroupRingDeterminant
variable (H : Type uH) [Group H]
local instance : DecidableEq H := Classical.decEq H

def fullIntToRat : MonoidAlgebra ℤ (LampGroup H) →+* MonoidAlgebra ℚ (LampGroup H) :=
  MonoidAlgebra.mapRingHom _ (Int.castRingHom ℚ)
def fullIntToBin : MonoidAlgebra ℤ (LampGroup H) →+* MonoidAlgebra (ZMod 2) (LampGroup H) :=
  MonoidAlgebra.mapRingHom _ (Int.castRingHom (ZMod 2))

lemma fullIntToRat_injective : Function.Injective (fullIntToRat H) :=
  MonoidAlgebra.map_injective (Int.castRingHom ℚ).toAddMonoidHom Int.cast_injective

lemma fullIntToRat_baseEmbedding (a : MonoidAlgebra ℤ (BaseGroup H)) :
    fullIntToRat H (baseEmbedding H ℤ a) = baseEmbedding H ℚ (intToRat H a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g z => simp [fullIntToRat, intToRat, baseEmbedding]

lemma numerator_toRat (S : Finset H) :
    fullIntToRat H (numerator H S) = (denominator H S : ℚ) • projection H S := by
  rw [numerator, fullIntToRat_baseEmbedding, intToRat_baseNumerator, map_rat_smul]
  rfl

lemma fullIntToRat_zsmul (a : MonoidAlgebra ℤ (LampGroup H)) (D : ℤ) :
    fullIntToRat H (D • a) = (D : ℚ) • fullIntToRat H a := by
  rw [Int.cast_smul_eq_zsmul]
  exact map_zsmul _ _ _

lemma fullIntToBin_zsmul (a : MonoidAlgebra ℤ (LampGroup H)) (D : ℤ) :
    fullIntToBin H (D • a) = (D : ZMod 2) • fullIntToBin H a := by
  rw [Int.cast_smul_eq_zsmul]
  exact map_zsmul _ _ _

lemma numerator_square (S : Finset H) :
    numerator H S * numerator H S = (denominator H S : ℤ) • numerator H S := by
  apply fullIntToRat_injective H
  rw [map_mul, fullIntToRat_zsmul, numerator_toRat, smul_mul_smul_comm,
    projection_idempotent, smul_smul]
  simp

lemma numerator_separates (S : Finset H) {s : H} (hs : s ∈ S) :
    numerator H S * shiftSymbol H s * numerator H S = 0 := by
  apply fullIntToRat_injective H
  rw [map_mul, map_mul, map_zero, numerator_toRat]
  have hs' : fullIntToRat H (shiftSymbol H s) = shiftSymbol H s := by
    simp [fullIntToRat, shiftSymbol]
  rw [hs', smul_mul_assoc, smul_mul_smul_comm, projection_separates H S hs, smul_zero]

def binaryProjection (S : Finset H) : MonoidAlgebra (ZMod 2) (LampGroup H) :=
  fullIntToBin H (numerator H S)

lemma binaryProjection_idempotent (S : Finset H) :
    IsIdempotentElem (binaryProjection H S) := by
  change fullIntToBin H _ * fullIntToBin H _ = fullIntToBin H _
  rw [← map_mul, numerator_square, fullIntToBin_zsmul, Int.cast_natCast,
    (denominator_odd H S).natCast_zmod_two, one_smul]

lemma binaryProjection_separates (S : Finset H) {s : H} (hs : s ∈ S) :
    binaryProjection H S * shiftSymbol H s * binaryProjection H S = 0 := by
  have he := congrArg (fullIntToBin H) (numerator_separates H S hs)
  simpa [binaryProjection, fullIntToBin, shiftSymbol] using he

end LampProjectionDraft

end

end OAI
