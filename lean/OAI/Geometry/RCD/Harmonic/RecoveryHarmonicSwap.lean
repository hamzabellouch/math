import OAI.Geometry.RCD.Sobolev.HarmonicCutoffSwap
import OAI.Geometry.RCD.Metric.RescaledCompactRepresentative

namespace OAI

/-! # The actual compact Dirichlet recovery is an admissible product test -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.recovery_harmonic_swap {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (f w q : SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) {r c S Q : ℝ} (hr : 0<r) (hcS : c<S) (hQ : 0≤Q)
    (hgrad : ∀ᵐ x ∂hausdorff n X,
      r^2*localGamma (hausdorff n X) hX.quadratic q q x≤Q^2)
    (hzero : ∀ᵐ x ∂hausdorff n X, x∉ball p (c*r) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic q x=0)
    (hw : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (S*r)) w) :
    (∫ x in ball p (S*r), SobolevSpace.toLp (hausdorff n X) hX.quadratic q x*
      localGamma (hausdorff n X) hX.quadratic f w x ∂hausdorff n X)=
      -(∫ x in ball p (S*r), SobolevSpace.toLp (hausdorff n X) hX.quadratic f x*
        localGamma (hausdorff n X) hX.quadratic q w x ∂hausdorff n X) := by
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨v,hv,hs,hvs,hrep⟩ := hX.rescaled_compact_representative hn q p hr hQ hgrad hzero
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hv.continuous
  have hb (x : X) : |v x|≤(⟨max B 0,le_max_right B 0⟩ : ℝ≥0) := by
    have hx : |v x|≤B := by simpa only [Real.norm_eq_abs] using hB x
    exact hx.trans (le_max_left B 0)
  have hswap := harmonic_signed_cutoff_swap μ hX.quadratic f w q hv hs hb hrep
    (hvs.trans (closedBall_subset_ball (mul_lt_mul_of_pos_right hcS hr))) hw
  have hout : ∀ᵐ x ∂μ, x∉ball p (S*r) → SobolevSpace.toLp μ hX.quadratic q x=0 :=
    hzero.mono fun x hx hy => hx (fun hc => hy
      ((ball_subset_ball (mul_le_mul_of_nonneg_right hcS.le hr.le)) hc))
  have hleft : (∫ x in ball p (S*r), SobolevSpace.toLp μ hX.quadratic q x*
      localGamma μ hX.quadratic f w x ∂μ)=
      ∫ x, v x*localGamma μ hX.quadratic f w x ∂μ := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (hout.mono fun x hx hy => by rw [hx hy,zero_mul])]
    exact integral_congr_ae (hrep.mono fun x hx => congrArg (fun t : ℝ => t*localGamma μ hX.quadratic f w x) hx)
  have hright : (∫ x in ball p (S*r), SobolevSpace.toLp μ hX.quadratic f x*
      localGamma μ hX.quadratic q w x ∂μ)=
      ∫ x, SobolevSpace.toLp μ hX.quadratic f x*localGamma μ hX.quadratic q w x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hout,localGamma_zero_on_level μ hX.quadratic q w 0] with x hx hγ hy
    rw [hγ (hx hy),mul_zero]
  rw [hleft,hright]
  exact hswap

end RegularPointCoordinates

end

end OAI
