import OAI.Analysis.Nuclearity.PureStateQuotient
import OAI.Analysis.Nuclearity.ProductPureSeparation
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws
import OAI.Analysis.PureInfiniteness.InnerHomCompression

namespace OAI

/-! Pullback of a product pure-state functional through quotient maps. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B C D : Type*}
  [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C] [CStarAlgebra D]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]

theorem exists_productPure_pullback
    (qA : A →⋆ₐ[ℂ] B) (qC : C →⋆ₐ[ℂ] D)
    (hA : Function.Surjective qA) (hC : Function.Surjective qC)
    (F : ProductPureFunctional B D) :
    ∃ G : ProductPureFunctional A C,
      ∀ z, G.functional z = F.functional
        (minimalMapAny qA.toNonUnitalStarAlgHom qC.toNonUnitalStarAlgHom z) := by
  obtain ⟨g, hg, hgp, hge⟩ := exists_pure_state_pullback qA hA F.leftState F.left_one F.left_pure
  obtain ⟨h, hh, hhp, hhe⟩ := exists_pure_state_pullback qC hC F.rightState F.right_one F.right_pure
  let q := minimalMapAny qA.toNonUnitalStarAlgHom qC.toNonUnitalStarAlgHom
  let L : MinimalTensor A C →L[ℂ] MinimalTensor B D := starHomContinuousLinear q
  let G := F.functional.comp L
  have hG : ‖G‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖F.functional (q z)‖ ≤ 1 * ‖z‖
    rw [one_mul]
    exact ((F.functional.le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right F.norm_le_one (norm_nonneg (q z)))).trans
      (NonUnitalStarAlgHom.norm_apply_le q z)
  refine ⟨{
    leftState := g
    rightState := h
    left_one := hg
    right_one := hh
    left_pure := hgp
    right_pure := hhp
    functional := G
    norm_le_one := hG
    elementary := ?_ }, fun _ => rfl⟩
  intro a c
  change F.functional (q (minimalElementary a c)) = _
  rw [minimalMapAny_elementary, F.elementary, hge, hhe]
  rfl

end WeakPureInfiniteness

end

end OAI
