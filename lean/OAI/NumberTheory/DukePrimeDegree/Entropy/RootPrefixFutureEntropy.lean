import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureFibers
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberEntropy
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixProductKernel

namespace OAI

/-! # Whole-future entropy from the actual intrinsic root products -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_cuts_with_rootPrefix_future_entropy (d : ℕ)
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
        conditionalSigmaEntropy (B.coordinateMeasure μ) (P ∘ F)
          (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) =
          ∫ z, observationEntropy
            ((anchorNormalize (B.intrinsicProductConditional μ z) (futureFiber T P F z)).restrict
              (futureFiber T P F z)) (fun t => P (F (z.1,t))) ∂B.coordinateMeasure μ := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨r,hr,hpos⟩ := exists_cuts_with_positive_rootPrefix_future_fibers
    d ell hell ε hε hgap μ hA C c hP₀ hf g B
  refine ⟨r,hr,?_⟩
  intro j
  have H := conditionalEntropy_futureFiber (B.coordinateMeasure μ)
    (continuous_rightAction (diagonalOneParameter ell hell (-1))).measurable
    (quotientCutObservation_measurable r j)
    (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable
    (show ∀ᵐ z ∂B.coordinateMeasure μ, (B.coordinateMeasure μ).condKernel z.1
      (futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
        (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z) ≠ 0 from by
      filter_upwards [hpos j] with z hz
      simpa only [futureFiber_eq_iInter,RootPrefixBox.conditionalKernel] using ne_of_gt hz)
  refine H.trans (integral_congr_ae ?_)
  filter_upwards [B.ae_conditionalKernel_eq_intrinsicProduct R hBR μ] with z hz
  change (B.coordinateMeasure μ).condKernel z.1 = B.intrinsicProductConditional μ z at hz
  rw [hz]

end DukePrimeDegree

end

end OAI
