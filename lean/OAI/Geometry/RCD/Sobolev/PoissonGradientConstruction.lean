import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.PoissonGradientBochner
import OAI.Geometry.RCD.Sobolev.PoissonGradientInput

namespace OAI

/-! # The Poisson gradient input from the retained RCD calculus -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Local truncation, Bochner interpolation and a countable interior cover
give the exact half-ball estimate at every permitted radius. -/
theorem NoncollapsedRCD.poissonGradientInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker)
    (hess : LocalPoissonHessianInput hX) : LocalPoissonGradientInput hX := by
  intro hn
  obtain ⟨M,hM,hlocal⟩ := hX.poisson_gradient_bochner hn hk hg hess
  refine ⟨4*M,by linarith,?_⟩
  intro p r hr hcurv f c A hA hf hAbound
  let : TopologicalSpace.SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let AA : ℝ≥0 := ⟨A,hA⟩
  obtain ⟨g,hg,hgA,hfg⟩ := hf.bounded_extension μ hX.quadratic measurableSet_ball AA hAbound
  have hpair := localGamma_pair_congr_ae μ hX.quadratic hfg hfg
  have hcurv' : -1 ≤ K*(r/4)^2 := by nlinarith only [hcurv]
  have hestimate (q : ball p (4*r)) :
      ∀ᵐ x ∂μ.restrict (ball q.val (r/8)),
        localGamma μ hX.quadratic f f x ≤ ((4*M)*(A/r+|c| *r))^2 := by
    have hq : dist q.val p < 4*r := q.property
    have hsub : ball q.val (8*(r/4)) ⊆ ball p (8*r) := ball_subset_ball' (by linarith)
    have hh := hlocal q.val (r/4) (by positivity) hcurv' g c AA
      (hg.mono μ hX.quadratic measurableSet_ball hsub) hgA
    rw [show (r/4)/2 = r/8 by ring] at hh
    have hsmall : ball q.val (r/8) ⊆ ball p (8*r) := ball_subset_ball' (by linarith)
    have hcoeff : M*(A/(r/4)+|c| *(r/4)) ≤ (4*M)*(A/r+|c| *r) := by
      have heq : A/(r/4) = 4*(A/r) := by ring
      rw [heq]
      nlinarith only [mul_nonneg (show 0 ≤ M by linarith) (mul_nonneg (abs_nonneg c) hr.le)]
    have hpow : (M*(A/(r/4)+|c| *(r/4)))^2 ≤ ((4*M)*(A/r+|c| *r))^2 :=
      pow_le_pow_left₀ (by positivity) hcoeff 2
    filter_upwards [hh,ae_restrict_of_ae_restrict_of_subset hsmall hpair] with x hx he
    rw [he]
    exact hx.trans hpow
  let U : ball p (4*r) → Set X := fun q => ball q.val (r/8)
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof (ball p (4*r))).elim_countable_subcover
    U (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff U hs _).mpr (fun q _ => hestimate q))

end RegularPointCoordinates

end

end OAI
