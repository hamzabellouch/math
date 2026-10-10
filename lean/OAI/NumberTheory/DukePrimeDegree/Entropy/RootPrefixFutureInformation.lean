import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberInformation

namespace OAI

/-! # Integrable future information in the intrinsic root product -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_cuts_with_rootPrefix_future_information (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    (C : RootPrefixCoordinates (d+1) P₀ V) (c : EliminationChain P₀ D)
    (hP₀ : InitialRootPattern P₀) (hf : c.finalEntries = allPositiveRoots (d+1))
    (g : G (d+1)) (B : RootPrefixBox C c hP₀ hf g)
    (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0) :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ j : ℕ,
        let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
        let P := quotientCutObservation (d := d+1) r j
        let F := C.timeParam c hP₀ hf g
        let I := fun z => -Real.log
          ((B.intrinsicProductConditional μ z).real
              ({t | P (F (z.1,t))=P (F z)} ∩ futureFiber T P F z) /
            (B.intrinsicProductConditional μ z).real (futureFiber T P F z))
        Integrable I (B.coordinateMeasure μ) ∧
          conditionalSigmaEntropy (B.coordinateMeasure μ) (P ∘ F)
            (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) =
              ∫ z, I z ∂B.coordinateMeasure μ := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨r,hr,hpos⟩ := exists_cuts_with_positive_rootPrefix_future_fibers
    d ell hell ε hε hgap μ hA C c hP₀ hf g B
  refine ⟨r,hr,?_⟩
  intro j
  have H := futureFiber_information_integrable_integral (B.coordinateMeasure μ)
    (continuous_rightAction (diagonalOneParameter ell hell (-1))).measurable
    (quotientCutObservation_measurable r j)
    (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable
    (show ∀ᵐ z ∂B.coordinateMeasure μ, (B.coordinateMeasure μ).condKernel z.1
      (futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
        (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z) ≠ 0 from by
      filter_upwards [hpos j] with z hz
      simpa only [futureFiber_eq_iInter,RootPrefixBox.conditionalKernel] using ne_of_gt hz)
  have heq : (fun z => -Real.log
      (((B.coordinateMeasure μ).condKernel z.1).real
          ({t | quotientCutObservation r j (C.timeParam c hP₀ hf g (z.1,t))=
            quotientCutObservation r j (C.timeParam c hP₀ hf g z)} ∩
              futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
                (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z) /
        ((B.coordinateMeasure μ).condKernel z.1).real
          (futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
            (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z))) =ᵐ[B.coordinateMeasure μ]
      (fun z => -Real.log
      ((B.intrinsicProductConditional μ z).real
          ({t | quotientCutObservation r j (C.timeParam c hP₀ hf g (z.1,t))=
            quotientCutObservation r j (C.timeParam c hP₀ hf g z)} ∩
              futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
                (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z) /
        (B.intrinsicProductConditional μ z).real
          (futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
            (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z))) := by
    filter_upwards [B.ae_conditionalKernel_eq_intrinsicProduct R hBR μ] with z hz
    change (B.coordinateMeasure μ).condKernel z.1 = B.intrinsicProductConditional μ z at hz
    rw [hz]
  exact ⟨H.1.congr heq,H.2.trans (integral_congr_ae heq)⟩

end DukePrimeDegree

end

end OAI
