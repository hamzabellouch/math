import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.LatticeDescendantGeometry
import OAI.Analysis.RieszRectifiability.Foundations.OriginalDyadicTests
import OAI.Analysis.RieszRectifiability.Foundations.OriginalOscillationWitness

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

abbrev BadSupportDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) :=
  {i : SupportCellDescendant μ R hR k z //
    ¬ ScalarOscillationBound n μ i.center (J * i.radius) (v * i.radius ^ (n + 1))}

def badCellWitness {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) (i : BadSupportDescendant n μ R hR k z J v) :
    OriginalOscillationWitness n μ i.val.center i.val.radius J v :=
  originalOscillationWitnessOfFailure n μ i.val.center i.val.radius J v i.val.radius_pos i.property

def badCellTestFamily {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    DyadicOscillationTests (BadSupportDescendant n μ R hR k z J v) d μ (1 / 8) J where
  center := fun i => i.val.center
  radius := fun i => i.val.radius
  level := fun i => i.val.binaryLevel
  test := fun i => (badCellWitness n μ R hR k z J v i).test
  lip := fun i => (badCellWitness n μ R hR k z J v i).lip
  radius_pos := fun i => i.val.radius_pos
  lipschitz := fun i => (badCellWitness n μ R hR k z J v i).lipschitz
  lip_bound := fun i => (badCellWitness n μ R hR k z J v i).lip_bound
  support_subset := fun i => (badCellWitness n μ R hR k z J v i).support_subset
  mean_zero := fun i => (badCellWitness n μ R hR k z J v i).mean_zero
  center_mem := fun i => i.val.center_mem_support
  core_admissible := fun i => i.val.core_admissible hcore
  scale_eq := fun i j hij => i.val.scale_eq j.val hij
  separated := fun i j hij hne => i.val.separated j.val hij (fun h => hne (Subtype.ext h))

theorem badCellTestFamily_large_pairing {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i : BadSupportDescendant n μ R hR k z J v) :
    v * (badCellTestFamily n μ R hR k z J v hcore).radius i ^ n <
      |rieszScalarPairing n μ ((badCellTestFamily n μ R hR k z J v hcore).center i)
        (2 * (J * (badCellTestFamily n μ R hR k z J v hcore).radius i))
        (badCellWitness n μ R hR k z J v i).direction
        ((badCellTestFamily n μ R hR k z J v hcore).test i)| :=
  (badCellWitness n μ R hR k z J v i).large_pairing

end

end RieszRectifiability

end OAI
