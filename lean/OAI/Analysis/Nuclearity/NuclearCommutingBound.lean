import OAI.Analysis.Nuclearity.CommutingMatrixNorm
import OAI.Analysis.WeakInfiniteness.NuclearTensorMap

namespace OAI

/-! A direct finite tensor norm bound for commuting representations of a
nuclear nonunital algebra. The proof uses only its matrix CP approximations. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {B C E : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C] [CStarAlgebra E]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [PartialOrder E] [StarOrderedRing E]

lemma nuclear_matrix_coordinates_norm_le {n : ℕ}
    (φ : B →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hφ : CompletelyPositive φ) (hφn : ‖φ‖ ≤ 1) (z : MinimalTensor B C) :
    ‖matrixTensorCoordinates (minimalCPMap φ z)‖ ≤ 4 * ‖z‖ := by
  have hm : ‖matrixTensorCoordinates (minimalCPMap φ z)‖ ≤ ‖minimalCPMap φ z‖ := by
    simpa only [matrixTensorCoordinates, one_mul] using LinearMap.norm_extendOfNorm_apply_le
      (tensorPolynomial_dense (A := CStarMatrix (Fin n) (Fin n) ℂ) (C := C))
      1
      (norm_matrixTensorPolynomial_le (n := Fin n) (C := C)) (minimalCPMap φ z)
  exact hm.trans ((norm_minimalCPMap_le φ hφ z).trans (by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
    nlinarith))

theorem nuclear_commuting_sum_norm_le (hB : Nuclear B)
    (π : B →⋆ₙₐ[ℂ] E) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    {I : Type*} (s : Finset I) (b : I → B) (c : I → C) :
    ‖∑ i ∈ s, π (b i) * η (c i)‖ ≤
      16 * ‖∑ i ∈ s, minimalElementary (b i) (c i)‖ := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let K : ℝ := ∑ i ∈ s, ‖c i‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let δ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n, hn, φ, ψ, hφ, hψ, hφn, hψn, happ⟩ := hB (s.image b) δ hδ
  let ψ' := (starHomContinuousLinear π).comp ψ
  have hψ' : CompletelyPositive ψ' := by
    intro m X hX
    have hp := map_nonneg (CStarMatrix.mapₙₐ π) (hψ m X hX)
    convert hp using 1
    ext i j
    rfl
  have hψ'n : ‖ψ'‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro M
    exact (NonUnitalStarAlgHom.norm_apply_le π (ψ M)).trans
      ((ψ.le_opNorm M).trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hψn (norm_nonneg M)))
  have hc' (i j : Fin n) (d : C) : Commute (ψ' (matrixUnit i j)) (η d) :=
    hc (ψ (matrixUnit i j)) d
  let z : MinimalTensor B C := ∑ i ∈ s, minimalElementary (b i) (c i)
  let w : CStarMatrix (Fin n) (Fin n) C := matrixTensorCoordinates (minimalCPMap φ z)
  have hw : w = ∑ i ∈ s, matrixTensorCoefficient (φ (b i)) (c i) := by
    simp only [w, z, map_sum, minimalCPMap_elementary φ hφ, matrixTensorCoordinates_elementary]
  have hΓ : commutingMatrixLinearMap ψ' η.toNonUnitalStarAlgHom w =
      ∑ i ∈ s, π (ψ (φ (b i))) * η (c i) := by
    rw [hw]
    simp only [map_sum, commutingMatrixLinearMap_coefficient]
    rfl
  have hbound : ‖∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ ≤ 16 * ‖z‖ := by
    rw [← hΓ]
    calc
      _ ≤ (4 * ‖ψ'‖) * ‖w‖ := commutingMatrixLinearMap_norm_le hn ψ' hψ' η hc' w
      _ ≤ (4 * 1) * (4 * ‖z‖) := by
        gcongr
        exact nuclear_matrix_coordinates_norm_le φ hφ hφn z
      _ = _ := by ring
  have herr : ‖(∑ i ∈ s, π (b i) * η (c i)) -
      ∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ ≤ δ * K := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ s, ‖π (b i) * η (c i) - π (ψ (φ (b i))) * η (c i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, δ * ‖c i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← sub_mul, ← map_sub]
        apply (norm_mul_le _ _).trans
        apply mul_le_mul
        · exact (NonUnitalStarAlgHom.norm_apply_le π _).trans (by
            simpa only [norm_sub_rev] using (happ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).le)
        · exact NonUnitalStarAlgHom.norm_apply_le η.toNonUnitalStarAlgHom _
        · exact norm_nonneg _
        · exact hδ.le
      _ = δ * K := (Finset.mul_sum s (fun i => ‖c i‖) δ).symm
  have he : δ * (K + 1) = ε := div_mul_cancel₀ ε (by positivity)
  have hlt : δ * K < ε := by nlinarith
  calc
    _ ≤ ‖(∑ i ∈ s, π (b i) * η (c i)) -
        ∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ +
        ‖∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ := norm_le_norm_sub_add _ _
    _ ≤ δ * K + 16 * ‖z‖ := add_le_add herr hbound
    _ ≤ _ := by change δ * K + 16 * ‖z‖ ≤ 16 * ‖z‖ + ε; linarith

end WeakPureInfiniteness

end

end OAI
