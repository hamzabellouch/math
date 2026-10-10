import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureStationarity
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixAmbientFuture

namespace OAI

/-! # Local stationarity of the ambient whole-future law

On a future-measurable event whose complete future fibers fit in the
box, the actual normalized intrinsic law on the ambient root orbit
recovers every ambient measurable event. This retains the local event
needed for gluing and makes no global stationarity assumption.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

theorem setIntegral_ambient_wholeFuture_probability
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (E : Set ((UpperRootTransverse (d+1) × V) × c.Time))
    (hE : MeasurableSet[⨆ m, transverseLabelSigma (fun z =>
      countableFutureCode (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
        Q m (C.timeParam c hP₀ hf g z))] E)
    (hcontained : ∀ᵐ z ∂(B.coordinateMeasure μ).restrict E,
      countableFutureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
        Q (C.timeParam c hP₀ hf g) z ⊆ B.time)
    (A : Set (X (d+1))) (hA : MeasurableSet A) :
    let F := C.timeParam c hP₀ hf g
    let κ := fun x =>
      ((anchorNormalize (c.remainingTimeProduct hP₀ hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))
    (∫ z in E, (κ (F z)).real A ∂B.coordinateMeasure μ) =
      (B.coordinateMeasure μ).real ((F ⁻¹' A) ∩ E) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP₀ hf g
  have hF : Measurable F :=
    (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable
  have H := B.setIntegral_uncentered_wholeFuture_probability R hBR μ hQ
    (continuous_rightAction _).measurable hgood E hE hcontained
    (F ⁻¹' A) (hA.preimage hF)
  refine (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)).trans H
  have hm := B.map_uncentered_future_eq_ambient μ ell hell Q 1 z
  refine (congrArg (fun ν : Measure (X (d+1)) => ν.real A) hm).symm.trans ?_
  change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
      (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).map
      (fun t => F (z.1,t)) A).toReal = _
  exact congrArg ENNReal.toReal (Measure.map_apply
    (show Measurable (fun t => F (z.1,t)) from hF.comp measurable_prodMk_left) hA)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
