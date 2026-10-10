import OAI.Analysis.KadisonSimilarity.FreeProduct.FreePrefixIsometry
import OAI.Analysis.KadisonSimilarity.Tracial.TracialHeadCoordinates

namespace OAI

/-! Surjectivity and left-action covariance of the first-factor tensor map. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem centered_word_mem_freeHead_range (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) {side : Bool} {xs : List P}
    (hxs : AlternatingCenteredWord G.trace A D side xs) :
    G.vector xs.prod ∈ Set.range (freeHeadIsometry G A D hτ hf) := by
  have ht (ys : CenteredWordParameter G A D true) :
      G.vector ys.1.prod ∈ Set.range (freeHeadIsometry G A D hτ hf) := by
    refine ⟨freeHeadTensor G A D (1, ys), ?_⟩
    rw [freeHeadIsometry_tensor, freeHeadVector, OneMemClass.coe_one, one_mul]
  cases side with
  | true => exact ht ⟨xs, hxs⟩
  | false =>
    cases hxs with
    | nil => exact ht ⟨[], .nil true⟩
    | @cons _ d ys hd _ hys =>
      refine ⟨freeHeadTensor G A D (⟨d, hd⟩, ⟨ys, hys⟩), ?_⟩
      exact freeHeadIsometry_tensor G A D hτ hf _

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
theorem freeHeadIsometry_surjective (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D) :
    Function.Surjective (freeHeadIsometry G A D hτ hf) := by
  let S := (freeHeadIsometry G A D hτ hf).toLinearMap.range
  have hs : centeredFreeWordSpan G A D ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨side, xs, hxs, rfl⟩
    exact centered_word_mem_freeHead_range G A D hτ hf hxs
  have hc : IsClosed (S : Set H) :=
    (freeHeadIsometry G A D hτ hf).isometry.isClosedEmbedding.isClosed_range
  have ht := (centeredFreeWordSpan G A D).topologicalClosure_minimal hs hc
  rw [centeredFreeWordSpan_dense G A D hτ hgen] at ht
  intro x
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

def freeHeadEquiv (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (hgen : ReducedWordGenerated G A D) :
    HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (freeHeadIsometry G A D hτ hf)
    (freeHeadIsometry_surjective G A D hτ hf hgen)

omit [IsClosed (A : Set P)] in
theorem freeHeadIsometry_covariance (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (d : D) (z : HilbertTensor (G.baseSpace D) (centeredWordSpace G A D true)) :
    freeHeadIsometry G A D hτ hf (tensorHeadAction ((G.baseGeometry D).left d) z) =
      G.left (d : P) (freeHeadIsometry G A D hτ hf z) := by
  let f := (freeHeadIsometry G A D hτ hf).toContinuousLinearMap.comp
      (tensorHeadAction ((G.baseGeometry D).left d)) -
    (G.left (d : P)).comp (freeHeadIsometry G A D hτ hf).toContinuousLinearMap
  have he : f = 0 := continuousLinearMap_eq_zero_of_total (freeHeadTensor G A D)
    (freeHeadTensor_total G A D) f (by
      rintro ⟨e, xs⟩
      change freeHeadIsometry G A D hτ hf
          (tensorHeadAction ((G.baseGeometry D).left d) (freeHeadTensor G A D (e, xs))) -
        G.left (d : P) (freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (e, xs))) = 0
      unfold freeHeadTensor
      rw [tensorHeadAction_insert]
      have hde : (G.baseGeometry D).left d (G.baseVector D e) = G.baseVector D (d * e) :=
        (G.baseGeometry D).left_vector d e
      rw [hde]
      change freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (d * e, xs)) -
        G.left (d : P) (freeHeadIsometry G A D hτ hf (freeHeadTensor G A D (e, xs))) = 0
      rw [freeHeadIsometry_tensor, freeHeadIsometry_tensor, freeHeadVector,
        freeHeadVector, G.left_vector]
      change G.vector (((d : P) * (e : P)) * xs.1.prod) -
        G.vector ((d : P) * ((e : P) * xs.1.prod)) = 0
      rw [mul_assoc, sub_self])
  exact sub_eq_zero.mp (congrArg (fun f => f z) he)

/-- The raw head coordinates of the reduced product, with their actual
left multiplication action. -/
def freeTracialHeadCoordinates (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (hgen : ReducedWordGenerated G A D) :
    TracialHeadCoordinates (G.baseGeometry D) G D.subtype (centeredWordSpace G A D true) where
  unitary := (freeHeadEquiv G A D hτ hf hgen).symm
  left_head d z := by
    apply (freeHeadEquiv G A D hτ hf hgen).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hc := freeHeadIsometry_covariance G A D hτ hf d
      ((freeHeadEquiv G A D hτ hf hgen).symm z)
    have hi : freeHeadIsometry G A D hτ hf
        ((freeHeadEquiv G A D hτ hf hgen).symm z) = z :=
      (freeHeadEquiv G A D hτ hf hgen).apply_symm_apply z
    rw [hi] at hc
    exact hc.symm

omit [IsClosed (A : Set P)] in
theorem freeTracialHeadCoordinates_vacuum (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D) :
    (freeTracialHeadCoordinates G A D hτ hf hgen).vacuum =
      (centeredWordSpace G A D true).toSubmodule := by
  have he (y : centeredWordSpace G A D true) :
      freeHeadEquiv G A D hτ hf hgen (hilbertTensorInsert (G.baseVector D 1) y) = (y : H) := by
    exact (freeHeadIsometry_left G A D hτ hf 1 y).trans (by
      simp only [OneMemClass.coe_one, map_one, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_apply])
  change (vacuumSubspace (G.baseVector D 1)).map
    (freeHeadEquiv G A D hτ hf hgen).toLinearIsometry.toLinearMap = _
  ext x
  constructor
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    change freeHeadEquiv G A D hτ hf hgen
      (hilbertTensorInsert (G.baseVector D 1) y) ∈ centeredWordSpace G A D true
    rw [he]
    exact y.property
  · intro hx
    refine ⟨hilbertTensorInsert (G.baseVector D 1) ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact he ⟨x, hx⟩

end KadisonSimilarity

end

end OAI
