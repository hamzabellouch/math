import OAI.Geometry.RCD.Sobolev.BoundedHilbertImageWeak
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace OAI

/-! # Measurability through an injective map of Hilbert spaces

The dense adjoint range transfers separability. The continuous injection
is then a Borel embedding, so measurable L2 realizations determine
measurable Sobolev-valued families.
-/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {E F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F] [MeasurableSpace Y]

theorem injective_hilbert_image_stronglyMeasurable
    (T : E →L[ℝ] F) (hT : Function.Injective T) (u : Y → E)
    (hu : StronglyMeasurable (fun y => T (u y))) : StronglyMeasurable u := by
  let : TopologicalSpace.SeparableSpace E :=
    (adjoint_denseRange_of_injective T hT).separableSpace T.adjoint.continuous
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have he : MeasurableEmbedding T := T.continuous.measurableEmbedding hT
  exact (he.measurable_comp_iff.mp hu.measurable).stronglyMeasurable

theorem injective_hilbert_image_aestronglyMeasurable
    (T : E →L[ℝ] F) (hT : Function.Injective T) (u : Y → E) (ν : Measure Y)
    (hu : AEStronglyMeasurable (fun y => T (u y)) ν) : AEStronglyMeasurable u ν := by
  let : TopologicalSpace.SeparableSpace E :=
    (adjoint_denseRange_of_injective T hT).separableSpace T.adjoint.continuous
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have he : MeasurableEmbedding T := T.continuous.measurableEmbedding hT
  obtain ⟨J,hJ,hJT⟩ := he.exists_measurable_extend (measurable_id : Measurable (id : E → E))
    (fun _ => ⟨0⟩)
  have hcomp : (fun y => J (T (u y))) = u := funext fun y => congrFun hJT (u y)
  rw [← hcomp]
  exact (hJ.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable

end RegularPointCoordinates

end

end OAI
