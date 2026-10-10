import Mathlib
import OAI.Analysis.WeakInfiniteness.VectorStates

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_compressed_real_state {b g : A} (hb : 0 ≤ b) (hg : IsSelfAdjoint g)
    (hgn : ‖g‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδb : δ ≤ ‖g*b*g‖) :
    ∃ f ∈ realStateSpace A,δ ≤ f ⟨b,hb.isSelfAdjoint⟩ ∧
      ∀ c : A, f ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩ ≤
        (‖b‖/δ)*‖c*g‖^2 := by
  have hgbg : 0 ≤ g*b*g := by simpa only [hg.star_eq] using star_right_conjugate_nonneg hb g
  have hgbgn : g*b*g ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hδb
    exact (not_le_of_gt hδ) hδb
  let : Nontrivial A := nontrivial_of_ne _ _ hgbgn
  obtain ⟨f,hf,hfb⟩ := exists_norming_real_state (g*b*g) hgbg
  let Φ := realStateComplexification f hf
  let π := Φ.gnsStarAlgHom
  let Ω := gnsCyclicVector Φ
  let ξ := π g Ω
  have hΩ : ‖Ω‖=1 := norm_gnsCyclicVector Φ (realStateComplexification_one f hf)
  have hvec : representationVectorFunctional π ξ ⟨b,hb.isSelfAdjoint⟩=‖g*b*g‖ := by
    have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf) ⟨g*b*g,hgbg.isSelfAdjoint⟩
    change (inner ℂ Ω (π (g*b*g) Ω)).re=f ⟨g*b*g,hgbg.isSelfAdjoint⟩ at he
    rw [hfb] at he
    change (inner ℂ (π g Ω) (π b (π g Ω))).re=_
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hs : (π g).adjoint=π g := by
      change star (π g)=π g
      rw [← map_star,hg.star_eq]
    rw [hs]
    simpa only [map_mul,mul_apply_eq_comp] using he
  have hξle : ‖ξ‖ ≤ 1 := calc
    ‖ξ‖ ≤ ‖π g‖*‖Ω‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖g‖*‖Ω‖ := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom g
    _ ≤ 1 := by rw [hΩ,mul_one]; exact hgn
  have hξ : ξ ≠ 0 := by
    intro hz
    change ‖g*b*g‖ ≥ δ at hδb
    have he : representationVectorFunctional π ξ ⟨b,hb.isSelfAdjoint⟩=0 := by
      simp [representationVectorFunctional,hz]
    rw [hvec] at he
    exact (not_le_of_gt hδ) (he ▸ hδb)
  have ht : 0 < ‖ξ‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have htone : ‖ξ‖^2 ≤ 1 := by nlinarith [norm_nonneg ξ]
  have hbnd : ‖g*b*g‖ ≤ ‖ξ‖^2*‖b‖ := by
    have he := (representationVectorFunctional π ξ).le_opNorm ⟨b,hb.isSelfAdjoint⟩
    rw [hvec,norm_norm] at he
    exact he.trans (mul_le_mul_of_nonneg_right (representationVectorFunctional_norm_le π ξ) (norm_nonneg b))
  have hinv : (‖ξ‖^2)⁻¹ ≤ ‖b‖/δ := by
    apply (le_div_iff₀ hδ).mpr
    apply (inv_mul_le_iff₀ ht).mpr
    nlinarith
  let F := StrongDual.toWeakDual ((‖ξ‖^2)⁻¹ • representationVectorFunctional π ξ)
  refine ⟨F,normalized_vector_mem_realStateSpace π hξ,?_,?_⟩
  · change δ ≤ (‖ξ‖^2)⁻¹*representationVectorFunctional π ξ ⟨b,hb.isSelfAdjoint⟩
    rw [hvec]
    apply (le_inv_mul_iff₀ ht).mpr
    exact (mul_le_of_le_one_left hδ.le htone).trans hδb
  · intro c
    change (‖ξ‖^2)⁻¹*representationVectorFunctional π ξ ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩ ≤ _
    rw [representationVectorFunctional_square]
    have hc : ‖π c ξ‖ ≤ ‖c*g‖ := calc
      _ = ‖π (c*g) Ω‖ := by rw [map_mul]; rfl
      _ ≤ ‖π (c*g)‖*‖Ω‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖c*g‖*‖Ω‖ := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _
      _ = ‖c*g‖ := by rw [hΩ,mul_one]
    exact mul_le_mul hinv (by nlinarith [norm_nonneg (π c ξ),norm_nonneg (c*g)])
      (sq_nonneg _) (div_nonneg (norm_nonneg b) hδ.le)

end

end WeakPureInfiniteness
end

end OAI
