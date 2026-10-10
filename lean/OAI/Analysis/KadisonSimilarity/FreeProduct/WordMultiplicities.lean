import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixRealization
import OAI.Analysis.KadisonSimilarity.Tensor.MultiplicityClassification

namespace OAI

/-! The actual multiplicity spaces of the alternating tracial words, their
normalized repeated-letter inclusions, and the degree-zero identification. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- The multiplicity of words with `k` centered base-algebra letters. -/
abbrev WordMultiplicity (ΩA : B) (k : ℕ) :=
  HilbertTensor (CompletedTensorWord (centeredSubspace ΩA) k) B

/-- A unit vector in the centered tensor power inserts the base Hilbert space
isometrically into the corresponding multiplicity space. -/
def multiplicityWordInclusion (ΩA : B) {k : ℕ}
    (w : CompletedTensorWord (centeredSubspace ΩA) k) (hw : ‖w‖ = 1) :
    B →ₗᵢ[ℂ] WordMultiplicity ΩA k where
  toLinearMap := (hilbertTensorInsert w).toLinearMap
  norm_map' b := by
    change ‖hilbertTensorInsert w b‖ = ‖b‖
    rw [norm_hilbertTensorInsert, hw, one_mul]

@[simp] theorem multiplicityWordInclusion_apply (ΩA : B) {k : ℕ}
    (w : CompletedTensorWord (centeredSubspace ΩA) k) (hw : ‖w‖ = 1) (b : B) :
    multiplicityWordInclusion ΩA w hw b = hilbertTensorInsert w b := rfl

/-- The repeated centered word `s ⊗ ⋯ ⊗ s`. -/
def repeatedMultiplicityWord (ΩA : B) (s : centeredSubspace ΩA) (k : ℕ) :
    CompletedTensorWord (centeredSubspace ΩA) k :=
  completedTensorWord (fun _ : Fin k => s)

@[simp] theorem norm_repeatedMultiplicityWord (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) (k : ℕ) : ‖repeatedMultiplicityWord ΩA s k‖ = 1 := by
  simp only [repeatedMultiplicityWord, norm_completedTensorWord, hs, Finset.prod_const_one]

/-- Insertion of a normalized repeated centered letter, with its exact norm. -/
def repeatedMultiplicityInclusion (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) (k : ℕ) : B →ₗᵢ[ℂ] WordMultiplicity ΩA k :=
  multiplicityWordInclusion ΩA (repeatedMultiplicityWord ΩA s k)
    (norm_repeatedMultiplicityWord ΩA s hs k)

@[simp] theorem repeatedMultiplicityInclusion_apply (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) (k : ℕ) (b : B) :
    repeatedMultiplicityInclusion ΩA s hs k b =
      hilbertTensorInsert (completedTensorWord (fun _ : Fin k => s)) b := rfl

/-- The empty centered word is the scalar unit in tensor degree zero. -/
def zeroMultiplicityWord (ΩA : B) : CompletedTensorWord (centeredSubspace ΩA) 0 :=
  completedTensorWord (Fin.elim0 : Fin 0 → centeredSubspace ΩA)

@[simp] theorem norm_zeroMultiplicityWord (ΩA : B) : ‖zeroMultiplicityWord ΩA‖ = 1 := by
  simp only [zeroMultiplicityWord, norm_completedTensorWord, Fin.prod_univ_zero]

/-- The canonical degree-zero inclusion of the base Hilbert space. -/
def zeroMultiplicityInclusion (ΩA : B) : B →ₗᵢ[ℂ] WordMultiplicity ΩA 0 :=
  multiplicityWordInclusion ΩA (zeroMultiplicityWord ΩA) (norm_zeroMultiplicityWord ΩA)

@[simp] theorem zeroMultiplicityInclusion_apply (ΩA : B) (b : B) :
    zeroMultiplicityInclusion ΩA b = hilbertTensorInsert (zeroMultiplicityWord ΩA) b := rfl

variable [CompleteSpace B]

/-- In degree zero the slice recovers every tensor, as proved from totality
of the completed empty word and of elementary Hilbert tensors. -/
theorem zeroMultiplicity_slice_inverse (ΩA : B) :
    (zeroMultiplicityInclusion ΩA).toContinuousLinearMap.comp
      (tensorSlice (zeroMultiplicityWord ΩA)) =
        ContinuousLinearMap.id ℂ (WordMultiplicity ΩA 0) := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro w b
  have hword :
      ((zeroMultiplicityInclusion ΩA).toContinuousLinearMap.comp
        (tensorSlice (zeroMultiplicityWord ΩA))).comp (hilbertTensorRightInsert b) =
          hilbertTensorRightInsert b := by
    apply continuousLinearMap_ext_completedTensorWords
    intro x
    have hx : completedTensorWord x = zeroMultiplicityWord ΩA := by
      congr 1
      funext i
      exact Fin.elim0 i
    change zeroMultiplicityInclusion ΩA
      (tensorSlice (zeroMultiplicityWord ΩA) (hilbertTensorInsert (completedTensorWord x) b)) =
        hilbertTensorInsert (completedTensorWord x) b
    rw [hx, tensorSlice_insert]
    have hunit : inner ℂ (zeroMultiplicityWord ΩA) (zeroMultiplicityWord ΩA) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, norm_zeroMultiplicityWord]
      norm_num
    rw [hunit, one_smul, zeroMultiplicityInclusion_apply]
  exact congrArg (fun T : CompletedTensorWord (centeredSubspace ΩA) 0 →L[ℂ]
    WordMultiplicity ΩA 0 => T w) hword

/-- No extra scalar tensor factor remains at word degree zero. -/
theorem zeroMultiplicityInclusion_surjective (ΩA : B) :
    Function.Surjective (zeroMultiplicityInclusion ΩA) := by
  intro z
  refine ⟨tensorSlice (zeroMultiplicityWord ΩA) z, ?_⟩
  exact congrArg (fun T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0 => T z)
    (zeroMultiplicity_slice_inverse ΩA)

/-- The actual unitary identification of the base space with multiplicity zero. -/
def zeroMultiplicityEquiv (ΩA : B) : B ≃ₗᵢ[ℂ] WordMultiplicity ΩA 0 :=
  LinearIsometryEquiv.ofSurjective (zeroMultiplicityInclusion ΩA)
    (zeroMultiplicityInclusion_surjective ΩA)

@[simp] theorem zeroMultiplicityEquiv_apply (ΩA : B) (b : B) :
    zeroMultiplicityEquiv ΩA b = hilbertTensorInsert (zeroMultiplicityWord ΩA) b := rfl

/-- Repeated insertion at degree zero is precisely the canonical unitary. -/
theorem repeatedMultiplicityInclusion_zero (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) :
    repeatedMultiplicityInclusion ΩA s hs 0 = (zeroMultiplicityEquiv ΩA).toLinearIsometry := by
  ext b
  change hilbertTensorInsert (completedTensorWord (fun _ : Fin 0 => s)) b =
    hilbertTensorInsert (completedTensorWord (Fin.elim0 : Fin 0 → centeredSubspace ΩA)) b
  congr 2

/-- Transport the canonical degree-zero block to an operator on the base space. -/
def zeroMultiplicityOperator (ΩA : B) (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0) :
    B →L[ℂ] B :=
  (zeroMultiplicityEquiv ΩA).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp (zeroMultiplicityEquiv ΩA).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem zeroMultiplicityOperator_intertwines (ΩA : B)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0) (b : B) :
    zeroMultiplicityEquiv ΩA (zeroMultiplicityOperator ΩA T b) =
      T (zeroMultiplicityEquiv ΩA b) := by
  change zeroMultiplicityEquiv ΩA ((zeroMultiplicityEquiv ΩA).symm _) = _
  exact (zeroMultiplicityEquiv ΩA).apply_symm_apply _

end KadisonSimilarity

end

end OAI
