import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.UpperRootFutureFibers

namespace OAI

/-! # Whole-future entropy in actual upper-root coordinate boxes -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_cuts_with_upperRoot_future_entropy (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (g : G (d+1)) (B : UpperRootBox (d+1) g) :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ j : ℕ,
        let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
        let P := quotientCutObservation (d := d+1) r j
        let F := upperRootQuotientParam (d+1) g
        conditionalSigmaEntropy (B.coordinateMeasure μ) (P ∘ F)
          (⨆ n, transverseLabelSigma (fun z => finiteFutureCode T P n (F z))) =
          ∫ z, observationEntropy
            ((anchorNormalize (B.conditionalKernel μ z.1) (futureFiber T P F z)).restrict
              (futureFiber T P F z)) (fun t => P (F (z.1,t))) ∂B.coordinateMeasure μ := by
  obtain ⟨r,hr,hpos⟩ := exists_cuts_with_positive_future_fibers d ell hell ε hε hgap μ hA g B
  refine ⟨r,hr,?_⟩
  intro j
  apply conditionalEntropy_futureFiber (B.coordinateMeasure μ)
    (continuous_rightAction _).measurable (quotientCutObservation_measurable r j)
    (upperRootQuotientParam_localHomeomorph (d+1) g).continuous.measurable
  filter_upwards [hpos j] with z hz
  simpa only [futureFiber_eq_iInter,UpperRootBox.conditionalKernel] using ne_of_gt hz

end DukePrimeDegree

end

end OAI
