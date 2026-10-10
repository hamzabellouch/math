import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalWindowProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalWindowRebase
import OAI.NumberTheory.DukePrimeDegree.Geometry.NextProductRegularity

namespace OAI

/-! # Centered physical-window conditionals are intrinsic product restrictions -/

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

theorem centeredConditional_intrinsic
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
      let V := (Homeomorph.mulLeft (c.remainingWordHomeomorph q.initial hf z.2)⁻¹) ''
        ((c.remainingWordHomeomorph q.initial hf) '' (B.toBox c hf).time)
      c.remainingGroupLeafMeasure q.initial hf
        (c.centeredRemainingMeasure q.initial hf ((B.toBox c hf).conditionalKernel μ z.1) z.2) =
        (anchorNormalize (c.remainingIntrinsicProduct q.initial hf μ
          (C.timeParam c q.initial hf g z)) V).restrict V := by
  have hAinv (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hroot := ae_intrinsicRootLeaf_spec q.distinct μ
    ((ae_root_stabilizer_trivial d μ hAinv).mono fun _ hx => hx _ _ _)
  filter_upwards [B.centeredConditional_product c hf c' hf' μ hfree hIH,
    (B.toBox c hf).ae_coordinate_of_ambient μ (q.ae_nextIntrinsicProduct_locallyFinite d μ),
    (B.toBox c hf).ae_coordinate_of_ambient μ hroot,
    (B.toBox c hf).ae_coordinate_of_ambient μ (q.ae_remainingIntrinsicProduct_factor d c hf μ)]
      with z hp hn hr hfactor
  let : IsLocallyFiniteMeasure (q.nextIntrinsicProduct d μ (C.timeParam c q.initial hf g z)) := hn
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf q.distinct μ (C.timeParam c q.initial hf g z)) := hr.1
  let E := RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf
  let a := E.symm z
  have ha : RootPrefixCoordinates.remainingFactorTime q c hf a.2 = z.2 :=
    congrArg Prod.snd (E.apply_symm_apply z)
  have H := B.normalized_product_on_group_time c hf
    (q.nextIntrinsicProduct d μ (C.timeParam c q.initial hf g z))
    (intrinsicRootLeaf q.distinct μ (C.timeParam c q.initial hf g z)) a.2
  dsimp only [InitialRootStep.remaining] at H
  erw [ha,←hfactor] at H
  exact hp.trans H

end PhysicalPrefixWindow
end DukePrimeDegree

end

end OAI
