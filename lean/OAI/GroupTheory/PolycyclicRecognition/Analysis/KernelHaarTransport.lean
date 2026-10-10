import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionMeasure
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # Haar measure on the actual quotient kernel

A closed realization of a Lie ideal identifies its intrinsic group with
the kernel. Equivariance transports conjugation invariance, and hence
also right invariance, to the measure used in section coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {I N Q : Type*} [Group I] [Group N] [Group Q]
  [TopologicalSpace I] [TopologicalSpace N] [IsTopologicalGroup I] [IsTopologicalGroup N]
  (π : N →* Q) (ι : I →* N) (hι : Topology.IsClosedEmbedding ι)
  (hrange : Set.range ι = (π.ker : Set N))

/-- The intrinsic ideal group and the actual kernel have the same topology
and multiplication. -/
def kernelRealization : I ≃ₜ* π.ker := by
  let e : I ≃ₜ π.ker := hι.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine { e with map_mul' := ?_ }
  intro x y
  apply Subtype.ext
  change ι (x * y) = ι x * ι y
  exact map_mul ι x y

omit [IsTopologicalGroup I] [IsTopologicalGroup N] in
@[simp] theorem kernelRealization_coe (x : I) :
    (kernelRealization π ι hι hrange x : N) = ι x := rfl

variable [MeasurableSpace I] [MeasurableSpace N] [BorelSpace I] [BorelSpace N]
  (μ : Measure I)

omit [IsTopologicalGroup I] in
/-- A concrete equivariant automorphism preserving intrinsic Haar measure
also preserves its image on the kernel. -/
theorem kernelRealization_conjugation_preserving (n : N) (F : I → I)
    (hF : MeasurePreserving F μ μ)
    (hequiv : ∀ x, ι (F x) = n * ι x * n⁻¹) :
    MeasurePreserving (quotientKernelConjugate π n)
      (Measure.map (kernelRealization π ι hι hrange) μ)
      (Measure.map (kernelRealization π ι hι hrange) μ) := by
  let e := kernelRealization π ι hι hrange
  have hsem : Function.Semiconj e F (quotientKernelConjugate π n) := by
    intro x
    apply Subtype.ext
    exact hequiv x
  have hc : Continuous (quotientKernelConjugate π n) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  exact (e.continuous.measurable.measurePreserving μ).of_semiconj hF hsem hc.measurable

/-- Left invariance together with the ambient conjugation invariance gives
the right invariance needed by the section cocycle. -/
theorem kernel_measure_right_invariant (ν : Measure π.ker) [ν.IsMulLeftInvariant]
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) ν ν) :
    ν.IsMulRightInvariant := by
  constructor
  intro k
  have hleft : MeasurePreserving (fun x : π.ker => k * x) ν ν :=
    ⟨(continuous_const.mul continuous_id).measurable, map_mul_left_eq_self ν k⟩
  have heq : (fun x : π.ker => k * quotientKernelConjugate π (k : N)⁻¹ x) =
      fun x => x * k := by
    funext x
    apply Subtype.ext
    change (k : N) * ((k : N)⁻¹ * x * ((k : N)⁻¹)⁻¹) = x * k
    group
  have hm := hleft.comp (hconj (k : N)⁻¹)
  change Measure.map (fun x : π.ker => x * k) ν = ν
  rw [← heq]
  exact hm.map_eq

end PolycyclicRecognition

end

end OAI
