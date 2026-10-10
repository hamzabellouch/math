import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixNullAmbient
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.SelfConditionalKernelMap

namespace OAI

/-! # Self-consistency of the ambient future kernel on quotient boxes -/

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
    [MeasurableSpace V] [BorelSpace V] [MeasurableSingletonClass V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

theorem selfConstant_image_massContained
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
    ∀ᵐ x ∂μ.restrict (F '' (E ∩ B.domain)), ∀ᵐ y ∂κ x, κ y=κ x := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP hf g
  let ρ := B.coordinateMeasure μ
  let K := B.regularLeafKernel R hBR μ hfree
  let E := {z | K z.1 (countableFutureFiber T Q F z \ B.time) = 0}
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  let η := futureFiberCoordinateKernel ρ.condKernel hT hQ hF
  have hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E :=
    measurableSet_future_mass_contained K hT hQ hF B.time B.time_open.measurableSet
  have hEle : (⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))) ≤
      (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
    apply iSup_le
    intro m
    exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
  have hEm : MeasurableSet E := hEle E hE
  have hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    exact ne_of_gt (hz.trans_le (measure_mono (fun t ht k => ht (k+1))))
  have hstat : (ρ.restrict E).bind η=ρ.restrict E :=
    futureFiberCoordinateKernel_stationary_restrict ρ hT hQ hF hpos E hE
  have hself : ∀ᵐ z ∂ρ.restrict E, ∀ᵐ w ∂η z, η w=η z :=
    Filter.Eventually.of_forall (futureFiberCoordinateKernel_self_constant ρ.condKernel hT hQ hF)
  have hversion : ∀ᵐ z ∂ρ.restrict E, κ (F z)=(η z).map F := by
    have hka := B.ae_coordinate_of_ambient μ hκ
    have hn := B.ae_normalized_uncentered_eq_regularLeaf R hBR μ hfree
    have hs := ae_of_ae_map measurable_fst.aemeasurable (B.ae_leafMeasure_spec R hBR μ hfree)
    have hk := ae_of_ae_map measurable_fst.aemeasurable (B.ae_regularLeafKernel_eq R hBR μ hfree)
    filter_upwards [ae_restrict_of_ae hka,ae_restrict_of_ae hn,
      ae_restrict_of_ae hs,ae_restrict_of_ae hk,ae_restrict_of_ae hpos,
      ae_restrict_mem hEm] with z hka hn hs hk hz hnull
    have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
      simp only [countableFutureFiber,Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_eq_fun
        (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
    have hmass : K z.1 B.time=1 := by
      change B.regularLeafKernel R hBR μ hfree z.1 B.time=1
      rw [hk]
      exact hs.2.1
    have hc : ρ.condKernel z.1=(anchorNormalize (K z.1) B.time).restrict B.time := by
      change B.conditionalKernel μ z.1=_
      rw [hk]
      simpa only [anchorNormalize,hs.2.1,inv_one,one_smul] using hs.2.2.1.symm
    have hnorm := normalized_restriction_of_null_diff (K z.1)
      (countableFutureFiber T Q F z) B.time hfuture B.time_open.measurableSet
      (by rw [hmass]; exact one_ne_zero) (by rw [hmass]; exact ENNReal.one_ne_top) hnull
    rw [hka,←B.map_uncentered_future_eq_ambient μ ell hell Q 1 z]
    change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
      (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).map
      (fun t => F (z.1,t)))=(η z).map F
    rw [hn]
    dsimp only [η]
    rw [futureFiberCoordinateKernel_apply,
      futureFiberTimeKernel_apply_good ρ.condKernel hT hQ hF z hz,
      Measure.map_map hF measurable_prodMk_left,hc,hnorm]
    rfl
  have H := selfConstant_kernel_map (ρ.restrict E) η hstat hself F hF κ hversion
  have hdom := B.coordinateMeasure_ae_domain μ
  have heq : ρ.restrict (E ∩ B.domain)=ρ.restrict E := by
    apply Measure.restrict_congr_set
    filter_upwards [hdom] with z hz
    simp only [mem_inter_iff,hz,and_true]
  have hm := B.map_restricted_coordinates μ (E ∩ B.domain)
    (hEm.inter (B.transverse_open.prod B.time_open).measurableSet) inter_subset_right
  rw [heq] at hm
  rwa [hm] at H

end RootPrefixBox
end DukePrimeDegree

end

end OAI
