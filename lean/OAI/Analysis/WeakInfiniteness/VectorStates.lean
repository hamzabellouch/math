import Mathlib
import OAI.Analysis.WeakInfiniteness.CStarClosedRange
import OAI.Analysis.WeakInfiniteness.PureStates

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

section VectorStates

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationVectorFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    selfAdjoint A →L[ℝ] ℝ where
  toFun b := (inner ℂ ξ (π (b : A) ξ)).re
  map_add' b c := by simp
  map_smul' r b := by
    change (inner ℂ ξ (π (r • (b : A)) ξ)).re=r • (inner ℂ ξ (π (b : A) ξ)).re
    rw [map_real_smul π (starHom_continuous π)]
    simp
  cont := by
    have hπ : Continuous π := starHom_continuous π
    fun_prop

lemma representationVectorFunctional_norm_le (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ‖representationVectorFunctional π ξ‖ ≤ ‖ξ‖^2 := by
  apply (representationVectorFunctional π ξ).opNorm_le_bound (sq_nonneg _)
  intro b
  change ‖(inner ℂ ξ (π (b : A) ξ)).re‖ ≤ ‖ξ‖^2*‖b‖
  calc
    _ ≤ ‖inner ℂ ξ (π (b : A) ξ)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (inner ℂ ξ (π (b : A) ξ))
    _ ≤ ‖ξ‖*‖π (b : A) ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖*(‖π (b : A)‖*‖ξ‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ξ‖*(‖(b : A)‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _
    _ = ‖ξ‖^2*‖b‖ := by change ‖ξ‖*(‖b‖*‖ξ‖)=_; ring

lemma representationVectorFunctional_one (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    representationVectorFunctional π ξ 1=‖ξ‖^2 := by
  change (inner ℂ ξ (π 1 ξ)).re=_
  rw [map_one,one_apply_eq_self]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

variable [PartialOrder A] [StarOrderedRing A]

lemma representationVectorFunctional_square (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    representationVectorFunctional π ξ ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩=
      ‖π a ξ‖^2 := by
  change (inner ℂ ξ (π (star a*a) ξ)).re=_
  rw [map_mul,map_star]
  change (inner ℂ ξ ((π a).adjoint (π a ξ))).re=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

omit [PartialOrder A] [StarOrderedRing A] in
lemma normalized_vector_mem_realStateSpace (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ξ ≠ 0) :
    (StrongDual.toWeakDual ((‖ξ‖^2)⁻¹ • representationVectorFunctional π ξ)) ∈ realStateSpace A := by
  have ht : 0 < ‖ξ‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  constructor
  · change ‖(‖ξ‖^2)⁻¹ • representationVectorFunctional π ξ‖ ≤ 1
    calc
      _ ≤ ‖(‖ξ‖^2)⁻¹‖*‖representationVectorFunctional π ξ‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = (‖ξ‖^2)⁻¹*‖representationVectorFunctional π ξ‖ := by
        rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      _ ≤ (‖ξ‖^2)⁻¹*(‖ξ‖^2) := mul_le_mul_of_nonneg_left
        (representationVectorFunctional_norm_le π ξ) (le_of_lt (inv_pos.mpr ht))
      _ = 1 := inv_mul_cancel₀ ht.ne'
  · change (‖ξ‖^2)⁻¹*representationVectorFunctional π ξ 1=1
    rw [representationVectorFunctional_one,inv_mul_cancel₀ ht.ne']

lemma gns_vectorFunctional_eq (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ realStateSpace A) :
    StrongDual.toWeakDual (representationVectorFunctional
      (realStateComplexification f hf).gnsStarAlgHom
      (gnsCyclicVector (realStateComplexification f hf)))=f := by
  apply DFunLike.ext
  intro b
  change (inner ℂ (gnsCyclicVector (realStateComplexification f hf))
    ((realStateComplexification f hf).gnsStarAlgHom (b : A)
      (gnsCyclicVector (realStateComplexification f hf)))).re=f b
  change (inner ℂ (((realStateComplexification f hf).toPreGNS 1) :
    (realStateComplexification f hf).GNS)
    ((realStateComplexification f hf).gnsNonUnitalStarAlgHom (b : A)
      ((realStateComplexification f hf).toPreGNS 1))).re=f b
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,UniformSpace.Completion.inner_coe]
  change ((realStateComplexification f hf) (star (1 : A)*((b : A)*1))).re=f b
  rw [star_one,one_mul,mul_one,realStateComplexification_apply,Complex.ofReal_re]

end VectorStates

end

end WeakPureInfiniteness
end

end OAI
