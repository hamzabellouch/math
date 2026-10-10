import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorParameter
import Mathlib.Topology.Sequences

namespace OAI

/-! Continuous bounded data for the fixed-power exterior contraction. -/

open Polynomial Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorResidualQuotient (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) : ℂ[X] :=
  Classical.choose (radialExteriorExpansion_residual ν n m j)

theorem radialExteriorResidualQuotient_spec (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    radialExteriorPolynomialResidual ν n (radialExteriorExpansion ν n m j)=
      X^j*radialExteriorResidualQuotient ν n m j :=
  Classical.choose_spec (radialExteriorExpansion_residual ν n m j)

theorem continuous_radialExteriorBase (n j : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun z : ℂ × ℂ =>
      boundedRadialPolynomialAfter T (radialExteriorExpansion z.1 n z.2 j)) := by
  apply SeqContinuous.continuous
  intro z z₀ hz
  exact radialExteriorBase_fixed_power_limit n j T hT z z₀ hz

theorem continuous_radialExteriorSource (n j : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun z : ℂ × ℂ =>
      boundedRadialResidualAfter T (radialExteriorResidualQuotient z.1 n z.2 j)) := by
  apply SeqContinuous.continuous
  intro z z₀ hz
  exact radialExteriorSource_fixed_power_limit n j T hT z z₀ hz _ _
    (fun i => radialExteriorResidualQuotient_spec _ _ _ _)
    (radialExteriorResidualQuotient_spec _ _ _ _)

theorem continuous_radialExteriorPolynomialJet (n j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Continuous (fun z : ℂ × ℂ => radialPolynomialJet (radialExteriorExpansion z.1 n z.2 j) t) := by
  apply SeqContinuous.continuous
  intro z z₀ hz
  apply (radialPolynomialJet_uniform_limit
    (fun i => radialExteriorExpansion (z i).1 n (z i).2 j)
    (radialExteriorExpansion z₀.1 n z₀.2 j) j
    (Eventually.of_forall (fun _ => radialExteriorExpansion_degree _ _ _ _))
    (radialExteriorExpansion_degree _ _ _ _) ?_).tendsto_at ht
  intro k _
  exact (continuous_radialExteriorExpansion_coeff n j k).continuousAt.tendsto.comp hz

end DefocusingNLS

end OAI
