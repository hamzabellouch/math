import OAI.Analysis.IrrationalRotation.Product.CoordinateSwap
import OAI.Analysis.IrrationalRotation.Sampling.ProductSampling

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel.Sampling

def reverseTriangularEvent (I : Finset ℕ) : Set EndpointPair :=
  {xz | ∀ i ∈ I, circleRepresentative (xz.2 i) < circleRepresentative (xz.1 i)}

theorem reverseTriangularEvent_measurable (I : Finset ℕ) :
    MeasurableSet (reverseTriangularEvent I) :=
  (triangularEvent_measurable I).preimage measurable_swap

theorem swap_preimage_reverseTriangularEvent (I : Finset ℕ) :
    CoordinateSwap.swapEquiv I ⁻¹' reverseTriangularEvent I = triangularEvent I := by
  ext xz
  change (∀ i ∈ I, circleRepresentative ((CoordinateSwap.swapEquiv I xz).2 i) <
    circleRepresentative ((CoordinateSwap.swapEquiv I xz).1 i)) ↔ _
  constructor
  · intro h i hi
    simpa only [CoordinateSwap.swapEquiv_snd, CoordinateSwap.swapEquiv_fst, ite_eq_left hi]
      using h i hi
  · intro h i hi
    simpa only [CoordinateSwap.swapEquiv_snd, CoordinateSwap.swapEquiv_fst, ite_eq_left hi]
      using h i hi

theorem triangularLaw_second_marginal_swap (I : Finset ℕ) :
    (triangularLaw I).map Prod.snd =
      ((baseMeasure.prod baseMeasure).restrict (reverseTriangularEvent I)).map Prod.fst := by
  have hp : MeasurePreserving (CoordinateSwap.swapEquiv (X := Circle) I)
      (baseMeasure.prod baseMeasure) (baseMeasure.prod baseMeasure) :=
    CoordinateSwap.measurePreserving_swap circleMeasure I
  have hm := hp.restrict_preimage (reverseTriangularEvent_measurable I)
  rw [swap_preimage_reverseTriangularEvent] at hm
  have heq : (fun xz : EndpointPair => selectedEndpoint I xz.1 xz.2) =
      Prod.fst ∘ CoordinateSwap.swapEquiv I := by
    funext xz i
    exact (CoordinateSwap.swapEquiv_fst I xz i).symm
  unfold triangularLaw
  rw [Measure.map_map measurable_snd (endpointMap_measurable I)]
  change ((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).map
    (fun xz : EndpointPair => selectedEndpoint I xz.1 xz.2) = _
  rw [heq, ← Measure.map_map measurable_fst (CoordinateSwap.swapEquiv I).measurable,
    hm.map_eq]

theorem triangularLaw_second_marginal (I : Finset ℕ) :
    (triangularLaw I).map Prod.snd =
      baseMeasure.withDensity (fun y => ENNReal.ofReal (triangularSecondDensity I y)) := by
  rw [triangularLaw_second_marginal_swap]
  exact reversedRestriction_first_marginal I

end Invariant233.ProductModel.Sampling

end OAI
