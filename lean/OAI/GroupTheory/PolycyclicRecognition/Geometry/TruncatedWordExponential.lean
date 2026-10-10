import OAI.GroupTheory.PolycyclicRecognition.Algebra.TruncatedRationalScalars
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PrimitiveNilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ScalarNilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordLieProjection

namespace OAI

/-! # The universal exponential product over truncated rational scalars -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

abbrev TruncatedWords (c n : ℕ) :=
  MonoidAlgebra (TruncatedRationalScalars c) (FreeMonoid (Fin n))

variable (c n : ℕ)

def truncatedWordLetter (i : Fin n) : TruncatedWords c n :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

def truncatedWordCoproduct : TruncatedWords c n →ₐ[TruncatedRationalScalars c]
    TruncatedWords c n ⊗[TruncatedRationalScalars c] TruncatedWords c n :=
  MonoidAlgebra.lift _ _ _ (FreeMonoid.lift (fun i =>
    truncatedWordLetter c n i ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
      (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] truncatedWordLetter c n i))

theorem truncatedWordCoproduct_letter (i : Fin n) :
    truncatedWordCoproduct c n (truncatedWordLetter c n i) =
      truncatedWordLetter c n i ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
        (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] truncatedWordLetter c n i := by
  simp [truncatedWordCoproduct, truncatedWordLetter, MonoidAlgebra.lift_single,
    FreeMonoid.lift_apply]

theorem truncatedWordCoproduct_parameter_letter (i : Fin n) :
    truncatedWordCoproduct c n (truncatedScalarParameter c • truncatedWordLetter c n i) =
      (truncatedScalarParameter c • truncatedWordLetter c n i) ⊗ₜ[TruncatedRationalScalars c]
        (1 : TruncatedWords c n) + (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c]
        (truncatedScalarParameter c • truncatedWordLetter c n i) := by
  simp only [map_smul, truncatedWordCoproduct_letter, smul_add,
    ← smul_tmul', tmul_smul]

def truncatedWordExponentialProduct : TruncatedWords c n :=
  (List.ofFn (fun i : Fin n =>
    IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i))).prod

theorem truncatedWordExponentialProduct_pow :
    (truncatedWordExponentialProduct c n - 1) ^ (c + 1) = 0 := by
  simpa only [List.map_ofFn, Function.comp_def, truncatedWordExponentialProduct]
    using scalar_nilpotent_exp_product_pow
    (truncatedScalarParameter c) (c + 1) (truncatedScalarParameter_pow c)
    (List.ofFn (truncatedWordLetter c n))

def truncatedWordLogarithm : TruncatedWords c n :=
  finiteNilpotentLog (c + 1) (truncatedWordExponentialProduct c n - 1)

theorem truncatedWordLogarithm_primitive :
    truncatedWordCoproduct c n (truncatedWordLogarithm c n) =
      truncatedWordLogarithm c n ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
        (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] truncatedWordLogarithm c n := by
  let L := List.ofFn (fun i : Fin n =>
    truncatedScalarParameter c • truncatedWordLetter c n i)
  have hL (a : TruncatedWords c n) (ha : a ∈ L) :
      IsNilpotent a ∧ truncatedWordCoproduct c n a =
        a ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
          (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] a := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨⟨c + 1, by rw [smul_pow, truncatedScalarParameter_pow, zero_smul]⟩,
      truncatedWordCoproduct_parameter_letter c n i⟩
  have hu := truncatedWordExponentialProduct_pow c n
  have h := log_product_nilpotentExp_primitive (truncatedWordCoproduct c n) L hL
    (show IsNilpotent ((L.map IsNilpotent.exp).prod - 1) from
      ⟨c + 1, by simpa only [L, List.map_ofFn, Function.comp_def,
        truncatedWordExponentialProduct] using hu⟩)
  have he : (L.map IsNilpotent.exp).prod = truncatedWordExponentialProduct c n := by
    simp only [L, List.map_ofFn, Function.comp_def, truncatedWordExponentialProduct]
  rw [he, nilpotentLog_eq_of_pow _ ⟨_, hu⟩ _ hu] at h
  exact h

end PolycyclicRecognition

end

end OAI
