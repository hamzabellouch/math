import OAI.Analysis.Nuclearity.MatrixFunctionalCP
import OAI.Analysis.Nuclearity.PositiveFunctionalExtension

namespace OAI

/-! Extension of a cpc map with finite matrix codomain along an injective
unital star homomorphism. The proof extends the associated positive scalar
functional and reconstructs the matrix map from its GNS representation. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B D : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra D]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder D] [StarOrderedRing D]

lemma cp_norm_le_one_of_one (φ : A →L[ℂ] D) (hφ : CompletelyPositive φ)
    (h1 : ‖φ 1‖ ≤ 1) : ‖φ‖ ≤ 1 := by
  apply cp_norm_le_one_of_positive_bound φ hφ
  intro a ha
  have hm : φ a ≤ φ (algebraMap ℝ A ‖a‖) := by
    have hp := completelyPositive_map_nonneg hφ
      (sub_nonneg.mpr (IsSelfAdjoint.le_algebraMap_norm_self a ha.isSelfAdjoint))
    simpa only [map_sub, sub_nonneg] using hp
  have he : φ (algebraMap ℝ A ‖a‖) = ‖a‖ • φ 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, Complex.coe_smul]
  rw [he] at hm
  calc
    ‖φ a‖ ≤ ‖‖a‖ • φ 1‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hm
      (completelyPositive_map_nonneg hφ ha)
    _ = ‖a‖ * ‖φ 1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_norm]
    _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    _ = ‖a‖ := mul_one _

variable {n : ℕ}

def matrixUnitalMap (ι : A →⋆ₐ[ℂ] B) :
    CStarMatrix (Fin n) (Fin n) A →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) B :=
  { CStarMatrix.mapₙₐ ι.toNonUnitalStarAlgHom with
    map_one' := by
      ext i j
      change ι (if i = j then (1 : A) else 0) = if i = j then (1 : B) else 0
      split_ifs <;> simp
    commutes' := fun c => by
      ext i j
      change ι (if i = j then algebraMap ℂ A c else 0) =
        if i = j then algebraMap ℂ B c else 0
      split_ifs
      · exact ι.commutes c
      · exact map_zero ι }

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma matrixUnitalMap_injective (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι) :
    Function.Injective (matrixUnitalMap (n := n) ι) := by
  intro M N h
  ext i j
  apply hι
  exact congrArg (fun P : CStarMatrix (Fin n) (Fin n) B => P i j) h

@[simp] lemma cpMatrixFunctional_single (p : Fin n)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ)
    (i j : Fin n) (a : A) :
    cpMatrixFunctional p φ hφ (matrixSingle i j a) = φ a i j := by
  have ht (k l : Fin n) : φ (matrixSingle i j a k l) k l =
      if i = k ∧ j = l then φ a k l else 0 := by
    change φ (if i = k ∧ j = l then a else 0) k l = _
    split_ifs <;> simp
  simp only [cpMatrixFunctional_apply, ht]
  change (∑ k, ∑ l, if i = k ∧ j = l then (CStarMatrix.ofMatrix.symm (φ a)) k l else 0) =
    (CStarMatrix.ofMatrix.symm (φ a)) i j
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp only [and_self, ite_true]
    · intro l _ hl
      simp only [Ne.symm hl, and_false, ite_false]
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    simp only [Ne.symm hk, false_and, ite_false]
  · simp

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] lemma matrixUnitalMap_single (ι : A →⋆ₐ[ℂ] B) (i j : Fin n) (a : A) :
    matrixUnitalMap ι (matrixSingle i j a) = matrixSingle i j (ι a) := by
  ext k l
  change ι (if i = k ∧ j = l then a else 0) = if i = k ∧ j = l then ι a else 0
  split_ifs <;> simp

theorem matrix_cpc_extension (p : Fin n) (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ)
    (hφn : ‖φ‖ ≤ 1) :
    ∃ Φ : B →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ,
      CompletelyPositive Φ ∧ ‖Φ‖ ≤ 1 ∧ ∀ a, Φ (ι a) = φ a := by
  obtain ⟨σ, hσ⟩ := positiveFunctional_extension (matrixUnitalMap ι)
    (matrixUnitalMap_injective ι hι) (cpMatrixFunctional p φ hφ)
  let Φ := matrixFunctionalCP p σ
  have hΦ : CompletelyPositive Φ := matrixFunctionalCP_completelyPositive p σ
  have he (a : A) : Φ (ι a) = φ a := by
    ext i j
    rw [matrixFunctionalCP_entry, ← matrixUnitalMap_single, hσ,
      cpMatrixFunctional_single]
  refine ⟨Φ, hΦ, cp_norm_le_one_of_one Φ hΦ ?_, he⟩
  have h1 := he 1
  rw [map_one] at h1
  rw [h1]
  exact (φ.le_opNorm 1).trans ((mul_le_mul hφn cstar_norm_one_le_one
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

end WeakPureInfiniteness

end

end OAI
