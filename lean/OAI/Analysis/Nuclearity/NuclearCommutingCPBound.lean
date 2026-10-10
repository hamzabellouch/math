import OAI.Analysis.Nuclearity.NuclearCommutingBound

namespace OAI

/-! The finite commuting tensor bound for completely positive maps on a nuclear
algebra. The approximation uses actual CP matrices, not centrality alone. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder
namespace WeakPureInfiniteness

variable {B C E : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C] [CStarAlgebra E]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [PartialOrder E] [StarOrderedRing E]

theorem nuclear_commuting_cp_sum_norm_le (hB : Nuclear B)
    (π : B →L[ℂ] E) (hπ : CompletelyPositive π) (η : C →⋆ₐ[ℂ] E) (hc : ∀ b c, Commute (π b) (η c))
    {I : Type*} (s : Finset I) (b : I → B) (c : I → C) :
    ‖∑ i ∈ s, π (b i) * η (c i)‖ ≤
      (16 * (‖π‖ + 1)) * ‖∑ i ∈ s, minimalElementary (b i) (c i)‖ := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let K : ℝ := ∑ i ∈ s, ‖c i‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let R := ‖π‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let δ := ε / (R * (K + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n, hn, φ, ψ, hφ, hψ, hφn, hψn, happ⟩ := hB (s.image b) δ hδ
  let ψ' := π.comp ψ
  have hψ' : CompletelyPositive ψ' := by
    intro m X hX
    have hp := hπ m (CStarMatrix.ofMatrix (fun i j => ψ (X i j))) (hψ m X hX)
    convert hp using 1
    ext i j
    rfl
  have hψ'n : ‖ψ'‖ ≤ R := by
    apply ContinuousLinearMap.opNorm_le_bound _ hR.le
    intro M
    calc
      _ ≤ ‖π‖ * ‖ψ M‖ := π.le_opNorm _
      _ ≤ R * (1 * ‖M‖) := by
        gcongr
        · dsimp [R]; linarith
        · exact (ψ.le_opNorm M).trans (mul_le_mul_of_nonneg_right hψn (norm_nonneg M))
      _ = R * ‖M‖ := by ring
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
  have hbound : ‖∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ ≤ (16 * R) * ‖z‖ := by
    rw [← hΓ]
    calc
      _ ≤ (4 * ‖ψ'‖) * ‖w‖ := commutingMatrixLinearMap_norm_le hn ψ' hψ' η hc' w
      _ ≤ (4 * R) * (4 * ‖z‖) := by
        gcongr
        exact nuclear_matrix_coordinates_norm_le φ hφ hφn z
      _ = _ := by ring
  have herr : ‖(∑ i ∈ s, π (b i) * η (c i)) -
      ∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ ≤ (R * δ) * K := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ s, ‖π (b i) * η (c i) - π (ψ (φ (b i))) * η (c i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, (R * δ) * ‖c i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← sub_mul, ← map_sub]
        apply (norm_mul_le _ _).trans
        apply mul_le_mul
        · calc
            _ ≤ ‖π‖ * ‖b i - ψ (φ (b i))‖ := π.le_opNorm _
            _ ≤ R * δ := by
              gcongr
              · dsimp [R]; linarith
              · simpa only [norm_sub_rev] using (happ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).le
        · exact NonUnitalStarAlgHom.norm_apply_le η.toNonUnitalStarAlgHom _
        · exact norm_nonneg _
        · exact mul_nonneg hR.le hδ.le
      _ = (R * δ) * K := (Finset.mul_sum s (fun i => ‖c i‖) (R * δ)).symm
  have he : (R * δ) * (K + 1) = ε := by
    calc
      _ = δ * (R * (K + 1)) := by ring
      _ = ε := div_mul_cancel₀ ε (by positivity)
  have hlt : (R * δ) * K < ε := by nlinarith [mul_pos hR hδ]
  calc
    _ ≤ ‖(∑ i ∈ s, π (b i) * η (c i)) -
        ∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ +
        ‖∑ i ∈ s, π (ψ (φ (b i))) * η (c i)‖ := norm_le_norm_sub_add _ _
    _ ≤ (R * δ) * K + (16 * R) * ‖z‖ := add_le_add herr hbound
    _ ≤ _ := by change (R * δ) * K + (16 * R) * ‖z‖ ≤ (16 * R) * ‖z‖ + ε; linarith

end WeakPureInfiniteness

end

end OAI
