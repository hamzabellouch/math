import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.Convert

namespace OAI

noncomputable section
open Polynomial
namespace SplittingSetup
abbrev Split (f : ℤ[X]) := (f.map (Int.castRingHom ℚ)).SplittingField
instance (f : ℤ[X]) : NumberField (Split f) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance
instance (f : ℤ[X]) : IsGalois ℚ (Split f) where
  to_isSeparable := inferInstance
  to_normal := by
    let : Algebra ℚ (Split f) := Polynomial.SplittingField.instAlgebra (f.map (Int.castRingHom ℚ))
    have h := Normal.of_isSplittingField (E := Split f) (f.map (Int.castRingHom ℚ))
    convert h using 1
lemma splits (f : ℤ[X]) : (f.map (Int.castRingHom (Split f))).Splits := by
  have hh := Polynomial.SplittingField.splits (f.map (Int.castRingHom ℚ))
  rw [Polynomial.map_map] at hh
  convert hh using 2
  congr 1
end SplittingSetup

end

end OAI
