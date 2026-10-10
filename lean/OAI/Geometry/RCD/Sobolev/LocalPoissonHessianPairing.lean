import OAI.Geometry.RCD.Sobolev.CompactPoissonHessian
import OAI.Geometry.RCD.Sobolev.LocalPoissonCompactExtension
import OAI.Geometry.RCD.Sobolev.HessianLocality

namespace OAI

/-! # Actual local Poisson Hessian pairings on every interior ball -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Bounded local gradients and the Poisson equations construct the full
integrated Hessian pairing, including a dense regular test core. -/
theorem NoncollapsedRCD.local_poisson_hessian_pairing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (f a : SobolevSpace (hausdorff n X) hX.quadratic) (c d : ℝ)
    {p : X} {r t : ℝ} (hr : 0<r) (ht : t≤2*r)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) a d)
    (L M : ℝ≥0)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L:ℝ)^2)
    (hM : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic a a x ≤ (M:ℝ)^2) :
    Nonempty (LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) f a) := by
  let μ := hausdorff n X
  obtain ⟨F,df,v,Q,hv,hvc,hFr,hdf,hF⟩ :=
    hX.local_poisson_compact_extension hn f c (R := 3*r) (by positivity) (by linarith) hf L hL
  obtain ⟨A,da,w,P,hw,hwc,hAr,hda,hA⟩ :=
    hX.local_poisson_compact_extension hn a d (R := 3*r) (by positivity) (by linarith) ha M hM
  have hsmall : ball p t ⊆ ball p (3*r) := ball_subset_ball (by linarith)
  have hlarge : ball p t ⊆ ball p (8*r) := ball_subset_ball (by linarith)
  have hF' := ae_restrict_of_ae_restrict_of_subset hsmall hF
  have hA' := ae_restrict_of_ae_restrict_of_subset hsmall hA
  have hFc := (hf.mono _ _ measurableSet_ball hlarge).congr_ae μ hX.quadratic
    measurableSet_ball (Filter.EventuallyEq.symm hF')
  have hAc := (ha.mono _ _ measurableSet_ball hlarge).congr_ae μ hX.quadratic
    measurableSet_ball (Filter.EventuallyEq.symm hA')
  obtain ⟨G⟩ := hX.compact_poisson_hessian_pairing hn p isOpen_ball F A
    hv hvc hFr hw hwc hAr df da hdf hda c d hFc hAc
  exact ⟨G.congr μ hX.quadratic measurableSet_ball hF' hA'⟩

end RegularPointCoordinates

end

end OAI
