import OAI.Analysis.KadisonKastler.WeakFieldKernel
import OAI.Analysis.FactorGeneration.SpectralPinching

namespace OAI

/-! # Spectral support inside measurable fields

The pointwise support of a continuous positive part is a measurable field.
This connects the constructed kernel projection with the concrete spectral
splittings already used in finite-factor arguments.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- The full concrete operator algebra. -/
def fullOperatorAlgebra : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' := Set.Subset.antisymm (Set.subset_univ _)
    Set.subset_centralizer_centralizer

local instance supportFieldOrder : PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance supportFieldStarOrder : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _
local instance supportOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance supportOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
local instance supportTopOrder : PartialOrder (fullOperatorAlgebra (H := H)).toStarSubalgebra :=
  CStarAlgebra.spectralOrder _
local instance supportTopStarOrder : StarOrderedRing (fullOperatorAlgebra (H := H)).toStarSubalgebra :=
  CStarAlgebra.spectralOrderedRing _

/-- The value of a field, viewed inside the full operator algebra. -/
def topElement (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    (fullOperatorAlgebra (H := H)).toStarSubalgebra := ⟨eval F x, by trivial⟩

@[simp] theorem topElement_val (F : WeakOperatorRepresentative (H := H) μ) (x : D) :
    (topElement F x).val = eval F x := rfl

theorem eval_posPart (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) (x : D) : eval (F⁺) x = (eval F x)⁺ := by
  change evalHom x (F⁺) = (evalHom x F)⁺
  simp only [CFC.posPart_def]
  exact NonUnitalStarAlgHomClass.map_cfcₙ (evalHom x) _ F
    (ha := hF) (hφa := hF.map (evalHom x))

private theorem topElement_posPart_val (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) (x : D) : ((topElement F x)⁺).val = eval (F⁺) x := by
  rw [eval_posPart F hF x]
  change (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype ((topElement F x)⁺) = _
  simp only [CFC.posPart_def]
  exact NonUnitalStarAlgHomClass.map_cfcₙ
    (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype _ (topElement F x)
    (ha := by
      apply IsSelfAdjoint.of_map (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
        Subtype.val_injective
      exact hF.map (evalHom x))
    (hφa := hF.map (evalHom x))

/-- Support of the positive part, as an actual measurable field. -/
def positiveSupport (F : WeakOperatorRepresentative (H := H) μ) :
    WeakOperatorRepresentative (H := H) μ :=
  1 - positiveKernelProjection (F⁺) (CFC.posPart_nonneg F)

theorem positiveSupport_isStarProjection (F : WeakOperatorRepresentative (H := H) μ) :
    IsStarProjection (positiveSupport F) :=
  (positiveKernelProjection_isStarProjection (F⁺) (CFC.posPart_nonneg F)).one_sub

/-- Evaluation agrees with the concrete range-projection construction. -/
theorem eval_positiveSupport (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) (x : D) :
    eval (positiveSupport F) x =
      ((Generator.Tracial.positiveSupport (topElement F x)).val).val := by
  have hs : (star ((topElement F x)⁺)).val = eval (F⁺) x := by
    rw [(CFC.posPart_nonneg (topElement F x)).isSelfAdjoint.star_eq]
    exact topElement_posPart_val F hF x
  change 1 - (eval (F⁺) x).ker.starProjection =
    1 - ((star ((topElement F x)⁺)).val).ker.starProjection
  rw [hs]

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
