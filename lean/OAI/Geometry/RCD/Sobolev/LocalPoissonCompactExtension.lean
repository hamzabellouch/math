import OAI.Geometry.RCD.Sobolev.PoissonCompactExtension
import OAI.Geometry.RCD.Sobolev.LocalGradientBoundedness
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent
import OAI.Geometry.RCD.Sobolev.PoissonLocality
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # Compact regular extensions from a local Poisson gradient bound -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_compact_extension {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ)
    {p : X} {R b : ℝ} (hR : 0<R) (hRb : 2*R<b)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p b) f c)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ)^2) :
    ∃ (F : SobolevSpace (hausdorff n X) hX.quadratic)
      (d : Lp ℝ 2 (hausdorff n X)) (v : X → ℝ) (Q : ℝ≥0),
      LipschitzWith Q v ∧ HasCompactSupport v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic F =ᵐ[hausdorff n X] v ∧
      IsWeakLaplacian (hausdorff n X) hX.quadratic F d ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic F =ᵐ[(hausdorff n X).restrict (ball p R)]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic f := by
  let μ := hausdorff n X
  let a := (2*R+b)/2
  have hab : a<b := by dsimp only [a]; linarith
  have hRa : 2*R<a := by dsimp only [a]; linarith
  have hsub : ball p a ⊆ ball p b := ball_subset_ball hab.le
  obtain ⟨A,hA⟩ := hX.local_amplitude_of_gradient hn f L hab hL
  obtain ⟨g,hg,hgA,hfg⟩ := (hf.mono _ _ measurableSet_ball hsub).bounded_extension μ hX.quadratic
    measurableSet_ball A (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hA)
  have hgL : ∀ᵐ x ∂μ.restrict (ball p a), localGamma μ hX.quadratic g g x ≤ (L:ℝ)^2 := by
    filter_upwards [localGamma_pair_congr_ae μ hX.quadratic hfg hfg,
      ae_restrict_of_ae_restrict_of_subset hsub hL] with x he hLx
    rw [← he]
    exact hLx
  obtain ⟨C,-,⟨χ⟩⟩ := hX.goodCutoff_exists hn p hR
  obtain ⟨F,d,v,Q,hv,hvc,hFv,hd,hFg,-⟩ := hX.poisson_compact_extension hn measurableSet_ball
    g c hg A L hgA hgL hR χ (closedBall_subset_ball hRa)
  refine ⟨F,d,v,Q,hv,hvc,hFv,hd,?_⟩
  exact hFg.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (show R≤a by linarith)) hfg))

end RegularPointCoordinates

end

end OAI
