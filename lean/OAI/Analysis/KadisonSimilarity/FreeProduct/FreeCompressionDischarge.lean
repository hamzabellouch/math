import OAI.Analysis.KadisonSimilarity.FreeProduct.CompressionProjectionTransport

namespace OAI

/-! The first-letter compression model on the concrete reduced product. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

def freeCompressionHead (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (hgen : ReducedWordGenerated G A D) :
    TracialHeadCoordinates (G.baseGeometry A) G A.subtype (centeredWordSpace G D A true) :=
  freeTracialHeadCoordinates G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen)

omit [IsClosed (D : Set P)] in
theorem freeCompressionAfterInclusion (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (hgen : ReducedWordGenerated G A D) :
    ((freeCompressionHead G A D hτ hf hgen).unitary.toLinearIsometry.comp
      (leadingWordSpace G D A true).toSubmodule.subtypeₗᵢ).toContinuousLinearMap =
      (hilbertTensorInsert (G.baseVector A 1)).comp
        (leadingIntoCentered G D A true).toContinuousLinearMap := by
  ext x
  change (freeCompressionHead G A D hτ hf hgen).unitary (x : H) =
    hilbertTensorInsert (G.baseVector A 1) (leadingIntoCentered G D A true x)
  apply (freeHeadEquiv G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen)).injective
  change (freeHeadEquiv G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen))
      ((freeHeadEquiv G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen)).symm (x : H)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  symm
  exact (freeHeadIsometry_left G D A hτ hf 1 (leadingIntoCentered G D A true x)).trans (by
    simp only [OneMemClass.coe_one, map_one, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply, leadingIntoCentered_coe])

def reducedWordCompressionModel (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (hgen : ReducedWordGenerated G A D) : ReducedWordCompressionModel G A D := by
  let W := freeCompressionHead G A D hτ hf hgen
  let U := W.unitary
  let S := centeredWordSpace G D A false
  let T := leadingWordSpace G D A true
  letI : CompleteSpace S.toSubmodule := S.isClosed.completeSpace_coe
  letI : CompleteSpace T.toSubmodule := T.isClosed.completeSpace_coe
  let j := leadingIntoCentered G D A true
  let v := U.toLinearIsometry.comp T.toSubmodule.subtypeₗᵢ
  let b := U.toLinearIsometry.comp S.toSubmodule.subtypeₗᵢ
  let c := freeCreationIsometry G D A D true rfl hτ hf
  have hST : S.toSubmoduleᗮ = T.toSubmodule :=
    centeredWordSpace_orthogonal G D A hτ hf (reducedWordGenerated_swap G A D hτ hgen) false
  have hp : firstLetterProjection (G.baseVector A 1) (isometryRangeProjection j) =
      isometryRangeProjection v :=
    firstLetterProjection_of_inclusion _ j v (freeCompressionAfterInclusion G A D hτ hf hgen)
  refine {
    tail := centeredWordSpace G D A true
    before := S
    head := W
    tailProjection := isometryRangeProjection j
    projection_adjoint := isometryRangeProjection_adjoint j
    projection_sq := isometryRangeProjection_sq j
    projection_norm := isometryRangeProjection_norm j
    includeBefore := b
    create := U.toLinearIsometry.comp c
    complement := ?_
    create_range := ?_
    create_word := ?_ }
  · change isometryRangeProjection b = 1 - firstLetterProjection (G.baseVector A 1)
      (isometryRangeProjection j)
    rw [hp]
    exact isometryRangeProjection_complement U S T hST
  · intro d hd x
    have hc : c (hilbertTensorInsert (G.baseSymmetryLetter D d hd) x) ∈ T :=
      freeCreationIsometry_mem G D A D true rfl hτ hf _
    let y : T := ⟨_, hc⟩
    change firstLetterProjection (G.baseVector A 1) (isometryRangeProjection j) (v y) = v y
    rw [hp, isometryRangeProjection_apply]
  · intro d hd x
    change U (G.left (d : P) (U.symm (U (x : H)))) =
      U (c (hilbertTensorInsert (G.baseSymmetryLetter D d hd) x))
    rw [U.symm_apply_apply]
    exact congrArg U (freeCreationIsometry_left G D A D true rfl hτ hf d hd x).symm

theorem ricardXuCompressionInput : RicardXuCompressionInput G A D := by
  intro hτ _ hf hgen
  exact ⟨reducedWordCompressionModel G A D hτ hf hgen⟩

end KadisonSimilarity

end

end OAI
