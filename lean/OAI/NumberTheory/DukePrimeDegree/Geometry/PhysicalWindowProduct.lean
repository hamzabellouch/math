import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalWindowAtlas
import OAI.NumberTheory.DukePrimeDegree.Entropy.PhysicalWindowConditionals

namespace OAI

/-! # The subgroup induction gives actual centered conditionals on large windows -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}
    (B : PhysicalPrefixWindow q C g)
    {D D' : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (c' : EliminationChain (insert q.root q.processed) D')
    (hf' : c'.finalEntries = allPositiveRoots (d+1))

theorem centeredConditional_product
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (hIH : ∀ m, ∀ A ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
        c' q.next_initial hf' g 1 m,
      ∀ᵐ z ∂A.coordinateMeasure μ,
        c'.remainingGroupLeafMeasure q.next_initial hf' (A.basedLeaf (1+m) μ z) =
          c'.remainingIntrinsicProduct q.next_initial hf' μ
            ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c' q.next_initial hf' g z)) :
    ∀ᵐ z ∂(B.toBox c hf).coordinateMeasure μ,
      let a := (RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf).symm z
      let x := C.timeParam c q.initial hf g z
      c.remainingGroupLeafMeasure q.initial hf
        (c.centeredRemainingMeasure q.initial hf ((B.toBox c hf).conditionalKernel μ z.1) z.2) =
        (((anchorNormalize (q.nextIntrinsicProduct d μ x)
          (q.nextFactorRebase d a.2.1 a.2.2 '' B.rectangle.second)).restrict
            (q.nextFactorRebase d a.2.1 a.2.2 '' B.rectangle.second)).prod
        ((anchorNormalize (intrinsicRootLeaf q.distinct μ x)
          (Homeomorph.addRight (-a.2.2) '' B.interval)).restrict
            (Homeomorph.addRight (-a.2.2) '' B.interval))).map q.remainingFactor := by
  let : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
  let : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
  obtain ⟨m,hm⟩ := B.exists_next_time_bound c' hf'
  have hAinv (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H := C.physicalPrefixMeasure_rebased_product q g B.pivot c' hf'
    B.rectangle B.box B.radius B.box_time_bound B.transverse_eq B.interval
    B.interval_open B.window μ hfree m hm (hIH m) (B.independent μ hAinv)
  let E := RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf
  rw [B.coordinateMeasure c hf μ]
  apply E.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [H,B.centeredConditional c hf μ] with a ha hc
  dsimp only
  rw [E.symm_apply_apply]
  change c.remainingGroupLeafMeasure q.initial hf
      (c.centeredRemainingMeasure q.initial hf ((B.toBox c hf).conditionalKernel μ a.1)
        (RootPrefixCoordinates.remainingFactorTime q c hf a.2)) = _
  rw [hc,RootPrefixCoordinates.physicalPrefixCoordinates_param q c hf C g]
  exact ha

end PhysicalPrefixWindow
end DukePrimeDegree

end

end OAI
