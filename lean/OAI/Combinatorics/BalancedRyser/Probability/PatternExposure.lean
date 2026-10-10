import OAI.Combinatorics.BalancedRyser.Probability.PatternExposureIdentities

namespace OAI

open MeasureTheory
universe u
namespace Balanced.PatternExposureReview5e39
variable (P : PatternModel.{u})

example (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation ∅ x (fun y => P.fixedExpectation K y P.count) =
      P.fixedExpectation ∅ x P.count :=
  PatternExposure.fixedExpectation_count_tower P (Finset.empty_subset K) x

example (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation K x (fun y => P.fixedExpectation K y P.count) =
      P.fixedExpectation K x P.count :=
  PatternExposure.fixedExpectation_count_tower P (Finset.Subset.refl K) x

example (x : P.Sample) :
    P.fixedExpectation Finset.univ x P.count = P.count x :=
  PatternExposure.fixedExpectation_count_of_support_subset P Finset.univ x
    (fun _ => Finset.subset_univ _)

example (x : P.Sample) (s : ℕ) (hs : 0 < s) :
    P.fixedExpectation Finset.univ x
      (fun y => |P.count y - P.fixedExpectation Finset.univ x P.count| ^ (2 * s)) = 0 :=
  PatternExposure.centeredMoment_zero_of_support_subset P Finset.univ x
    (fun _ => Finset.subset_univ _) s hs

example (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation K x
      (fun y => |P.count y - P.fixedExpectation K x P.count| ^ (2 * 0)) = 1 := by
  simp [PatternModel.fixedExpectation]

example (x : P.Sample) (h : ∀ a, P.support a = ∅) :
    P.fixedExpectation ∅ x P.count = P.count x :=
  PatternExposure.fixedExpectation_count_of_support_subset P ∅ x
    (fun a => by rw [h a])
end Balanced.PatternExposureReview5e39

end OAI
