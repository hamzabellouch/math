import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.SmallScalePoissonGradient
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! # Interior Poisson estimates for locally bounded solutions at small radii -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The half-ball form of the Poisson estimate for radii at most one.
The amplitude hypothesis is local; global truncation is internal. -/
theorem NoncollapsedRCD.poisson_gradient_at_small_radii {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r → r ≤ 1 → -1 ≤ K*r^2 →
      ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (c A : ℝ), 0 ≤ A →
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)), |SobolevSpace.toLp _ _ f x| ≤ A) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4*r)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ (C*(A/r+|c| *r))^2 := by
  obtain ⟨M,hM,hlocal⟩ := hX.small_scale_poisson_gradient hn hk hg
  refine ⟨16*M,by linarith,?_⟩
  intro p r hr hr1 hcurv f c A hA hf hAbound
  let : TopologicalSpace.SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let AA : ℝ≥0 := ⟨A,hA⟩
  obtain ⟨g,hg,hgA,hfg⟩ := hf.bounded_extension μ hX.quadratic measurableSet_ball AA hAbound
  have hpair := localGamma_pair_congr_ae μ hX.quadratic hfg hfg
  have hcurv' : -1 ≤ K*(4*(r/16))^2 := by nlinarith only [hcurv]
  have hC0 : 0 ≤ 16*M := by linarith
  have hestimate (q : ball p (4*r)) :
      ∀ᵐ x ∂μ.restrict (ball q.val (r/256)),
        localGamma μ hX.quadratic f f x ≤ ((16*M)*(A/r+|c| *r))^2 := by
    have hq : dist q.val p < 4*r := q.property
    have hsub : ball q.val (16*(r/16)) ⊆ ball p (8*r) :=
      ball_subset_ball' (by linarith)
    have hh := hlocal q.val (r/16) (by positivity) (by linarith) hcurv' g c AA
      (hg.mono μ hX.quadratic measurableSet_ball hsub) hgA
    rw [show (r/16)/16 = r/256 by ring] at hh
    have hsmall : ball q.val (r/256) ⊆ ball p (8*r) :=
      ball_subset_ball' (by linarith)
    have hcoeff : M*(A/(r/16)+|c| *(r/16)) ≤ (16*M)*(A/r+|c| *r) := by
      have heq : A/(r/16) = 16*(A/r) := by ring
      rw [heq]
      nlinarith only [mul_nonneg (show 0 ≤ M by linarith) (mul_nonneg (abs_nonneg c) hr.le)]
    have hpow : (M*(A/(r/16)+|c| *(r/16)))^2 ≤ ((16*M)*(A/r+|c| *r))^2 :=
      pow_le_pow_left₀ (by positivity) hcoeff 2
    filter_upwards [hh,ae_restrict_of_ae_restrict_of_subset hsmall hpair] with x hx he
    rw [he]
    exact hx.trans hpow
  let U : ball p (4*r) → Set X := fun q => ball q.val (r/256)
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof (ball p (4*r))).elim_countable_subcover
    U (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff U hs _).mpr (fun q _ => hestimate q))

end RegularPointCoordinates

end

end OAI
