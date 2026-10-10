import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixNullStationarity
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixAmbientFuture
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixStationaryImages

namespace OAI

/-! # Ambient stationarity on local mass-containment events -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

theorem stationary_image_massContained
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hκ : ∀ᵐ x ∂μ, κ x =
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP hf g
    let E := {z | B.regularLeafKernel R hBR μ hfree z.1
      (countableFutureFiber T Q F z \ B.time) = 0}
    (μ.restrict (F '' (E ∩ B.domain))).bind κ =
      μ.restrict (F '' (E ∩ B.domain)) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP hf g
  let K := B.regularLeafKernel R hBR μ hfree
  let E := {z | K z.1 (countableFutureFiber T Q F z \ B.time) = 0}
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hE : MeasurableSet E := by
    have he := measurableSet_future_mass_contained K hT hQ hF B.time
      B.time_open.measurableSet
    have hle : (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) ≤
        (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
      apply iSup_le
      intro m
      exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
    exact hle E he
  apply B.stationary_image_of_local_event μ κ E hE
  intro A hA
  have H := B.setIntegral_massContained_wholeFuture_probability R hBR μ hfree hQ hT
    hgood (F ⁻¹' A) (hA.preimage hF)
  refine (integral_congr_ae ?_).trans H
  have hka := B.ae_coordinate_of_ambient μ hκ
  have hnorm := B.ae_normalized_uncentered_eq_regularLeaf R hBR μ hfree
  filter_upwards [ae_restrict_of_ae hka, ae_restrict_of_ae hnorm] with z hz hn
  rw [hz, ← B.map_uncentered_future_eq_ambient μ ell hell Q 1 z]
  change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
    (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).map
      (fun t => F (z.1,t))).real A = _
  rw [hn]
  exact congrArg ENNReal.toReal (Measure.map_apply
    (show Measurable (fun t => F (z.1,t)) from hF.comp measurable_prodMk_left) hA)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
