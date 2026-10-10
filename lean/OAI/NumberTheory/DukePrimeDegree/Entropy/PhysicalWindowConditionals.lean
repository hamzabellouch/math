import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixWindows
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalProductRebase

namespace OAI

/-! # Actual prefix conditionals on a physical product window -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}
    (B : PhysicalPrefixWindow q C g)
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

lemma coordinateMeasure (μ : Measure (X (d+1))) :
    (B.toBox c hf).coordinateMeasure μ =
      (C.physicalPrefixMeasure q g B.pivot B.rectangle B.box B.interval μ).map
        (RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf) :=
  C.physicalPrefixBox_coordinateMeasure q c hf g B.pivot B.rectangle B.box
    B.transverse_eq B.interval B.interval_open B.window μ

theorem conditionalKernel (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    let θ := C.physicalPrefixMeasure q g B.pivot B.rectangle B.box B.interval μ
    ∀ᵐ s ∂θ.fst, (B.toBox c hf).conditionalKernel μ s =
      (θ.condKernel s).map (RootPrefixCoordinates.remainingFactorTime q c hf) := by
  intro θ
  let E := RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf
  let W := RootPrefixCoordinates.remainingFactorTime q c hf
  have H := conditional_map_fibers_embedding θ id MeasurableEmbedding.id
    (fun z => W z.2) (W.measurable.comp measurable_snd)
  have hm : θ.map E = (B.toBox c hf).coordinateMeasure μ := (B.coordinateMeasure c hf μ).symm
  have H' : ∀ᵐ s ∂θ.fst, (θ.map E).condKernel s = (θ.condKernel s).map W := H
  simpa only [hm,RootPrefixBox.conditionalKernel] using H'

theorem groupConditional (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    let θ := C.physicalPrefixMeasure q g B.pivot B.rectangle B.box B.interval μ
    ∀ᵐ s ∂θ.fst,
      ((B.toBox c hf).conditionalKernel μ s).map (c.remainingWordHomeomorph q.initial hf) =
        (θ.condKernel s).map q.remainingFactor := by
  intro θ
  filter_upwards [B.conditionalKernel c hf μ] with s hs
  rw [hs,Measure.map_map (c.remainingWordHomeomorph q.initial hf).measurable
    (RootPrefixCoordinates.remainingFactorTime q c hf).measurable]
  congr 1
  funext z
  change (c.remainingWordHomeomorph q.initial hf)
    ((c.remainingWordHomeomorph q.initial hf).symm (q.remainingFactor z)) = _
  exact (c.remainingWordHomeomorph q.initial hf).apply_symm_apply _

theorem centeredConditional (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    let θ := C.physicalPrefixMeasure q g B.pivot B.rectangle B.box B.interval μ
    ∀ᵐ z ∂θ,
      c.remainingGroupLeafMeasure q.initial hf
        (c.centeredRemainingMeasure q.initial hf ((B.toBox c hf).conditionalKernel μ z.1)
          (RootPrefixCoordinates.remainingFactorTime q c hf z.2)) =
        ((θ.condKernel z.1).map q.remainingFactor).map
          (Homeomorph.mulLeft (q.remainingFactor z.2)⁻¹) := by
  intro θ
  have H := ae_of_ae_map measurable_fst.aemeasurable (B.groupConditional c hf μ)
  filter_upwards [H] with z hz
  have he : (c.remainingWordHomeomorph q.initial hf)
      (RootPrefixCoordinates.remainingFactorTime q c hf z.2) = q.remainingFactor z.2 :=
    (c.remainingWordHomeomorph q.initial hf).apply_symm_apply _
  rw [c.groupLeafMeasure_centered]
  change (((B.toBox c hf).conditionalKernel μ z.1).map
    (c.remainingWordHomeomorph q.initial hf)).map (Homeomorph.mulLeft
      (c.remainingWordHomeomorph q.initial hf (RootPrefixCoordinates.remainingFactorTime q c hf z.2))⁻¹) = _
  erw [hz,he]
  rfl

end PhysicalPrefixWindow
end DukePrimeDegree

end

end OAI
