import OAI.Geometry.RCD.Coordinates.OpenRegularCutoff
import OAI.Geometry.RCD.Sobolev.FiniteEnergyRepresentatives

namespace OAI

/-! # Bounded Sobolev representatives of constants on a fixed ball -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A compact regular plateau represents the local constant without
requiring a globally square-integrable constant function. -/
theorem NoncollapsedRCD.local_constant_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (p : X) (R c : ℝ) :
    ∃ d : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic d x|≤‖c‖₊) ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic d
        =ᵐ[(hausdorff n X).restrict (ball p R)] fun _ => c := by
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  obtain ⟨χ,-,hχ1⟩ := hX.exists_open_regular_cutoff hn isOpen_univ (isCompact_closedBall p R) (subset_univ _)
  have hrep := sobolev_smul_representative μ hX.quadratic c
    (Ω := univ) (by simpa only [Measure.restrict_univ] using χ.representative)
  have hr : SobolevSpace.toLp μ hX.quadratic (c • χ.sobolev)
      =ᵐ[μ] fun x => c*χ.weight x := by simpa only [Measure.restrict_univ] using hrep
  refine ⟨c • χ.sobolev,?_,?_⟩
  · filter_upwards [hr] with x hx
    rw [hx,abs_mul,coe_nnnorm,Real.norm_eq_abs]
    calc
      |c| * |χ.weight x| ≤ |c| * 1 := mul_le_mul_of_nonneg_left (χ.abs_le x) (abs_nonneg c)
      _ = |c| := mul_one _
  · filter_upwards [ae_restrict_of_ae hr,ae_restrict_mem measurableSet_ball] with x hx hm
    rw [hx,hχ1 x (ball_subset_closedBall hm),mul_one]

end RegularPointCoordinates

end

end OAI
