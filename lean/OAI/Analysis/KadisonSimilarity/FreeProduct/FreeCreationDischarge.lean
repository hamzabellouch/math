import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCreationOperators
import OAI.Analysis.KadisonSimilarity.FreeProduct.PublishedWordCreation

namespace OAI

/-! The two elementary creation maps in the published interface, constructed
on the actual tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

section TensorMap
variable {E F K L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

def hilbertTensorMapIsometry (f : E →ₗᵢ[ℂ] K) (g : F →ₗᵢ[ℂ] L) :
    HilbertTensor E F →ₗᵢ[ℂ] HilbertTensor K L := (TensorProduct.mapIsometry f g).completion

@[simp] theorem hilbertTensorMapIsometry_insert (f : E →ₗᵢ[ℂ] K) (g : F →ₗᵢ[ℂ] L)
    (x : E) (y : F) : hilbertTensorMapIsometry f g (hilbertTensorInsert x y) =
      hilbertTensorInsert (f x) (g y) := by
  change (TensorProduct.mapIsometry f g).completion
    ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : UniformSpace.Completion (E ⊗[ℂ] F)) = _
  rw [LinearIsometry.completion_apply_coe, TensorProduct.mapIsometry_apply,
    TensorProduct.map_tmul]
  rfl

end TensorMap

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

omit [IsClosed (A : Set P)] in
theorem freeHead_vacuum_orthogonal (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    (freeTracialHeadCoordinates G A D hτ hf.symm hgen).vacuumᗮ =
      (leadingWordSpace G A D false).toSubmodule := by
  rw [freeTracialHeadCoordinates_vacuum]
  exact centeredWordSpace_orthogonal G A D hτ hf.symm hgen true

def reducedWordCreationModel (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    ReducedWordCreationModel G A D := by
  let W := freeTracialHeadCoordinates G A D hτ hf.symm hgen
  let e := LinearIsometryEquiv.ofEq W.vacuumᗮ (leadingWordSpace G A D false).toSubmodule
    (freeHead_vacuum_orthogonal G A D hτ hf hgen)
  let cA := freeCreationIsometry G A D A true rfl hτ hf.symm
  let cD := freeCreationIsometry G A D D false rfl hτ hf.symm
  let iA := (leadingIntoCentered G A D false).comp e.toLinearIsometry
  refine {
    tail := centeredWordSpace G A D true
    head := W
    aLead := leadingWordSpace G A D true
    createA := cA.comp (hilbertTensorMapIsometry (LinearIsometry.id) iA)
    createD := cD.comp (hilbertTensorMapIsometry (LinearIsometry.id) (leadingIntoCentered G A D true))
    createA_mem := ?_
    createD_mem := ?_
    actionA := ?_
    actionD := ?_ }
  · intro z
    exact freeCreationIsometry_mem G A D A true rfl hτ hf.symm _
  · intro z
    rw [freeHead_vacuum_orthogonal G A D hτ hf hgen]
    exact freeCreationIsometry_mem G A D D false rfl hτ hf.symm _
  · intro a ha y
    change G.left (a : P) (y : H) = cA
      (hilbertTensorMapIsometry (LinearIsometry.id) iA
        (hilbertTensorInsert (G.baseSymmetryLetter A a ha) y))
    rw [hilbertTensorMapIsometry_insert]
    exact (freeCreationIsometry_left G A D A true rfl hτ hf.symm a ha (iA y)).symm
  · intro d hd y
    change G.left (d : P) (y : H) = cD
      (hilbertTensorMapIsometry (LinearIsometry.id) (leadingIntoCentered G A D true)
        (hilbertTensorInsert (G.baseSymmetryLetter D d hd) y))
    rw [hilbertTensorMapIsometry_insert]
    exact (freeCreationIsometry_left G A D D false rfl hτ hf.symm d hd
      (leadingIntoCentered G A D true y)).symm

theorem ricardXuCreationInput : RicardXuCreationInput G A D := by
  intro hτ _ hf hgen
  exact ⟨reducedWordCreationModel G A D hτ hf hgen⟩

end KadisonSimilarity

end

end OAI
