import OAI.Geometry.RCD.Heat.HeatGamma
import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Sobolev sources and Gram functions of a bounded-gradient heat state -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X]

theorem NoncollapsedRCD.heat_regular_source_gram {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) {t : ℝ} (ht : 0<t) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic t ht f) x≤L) :
    ∃ (D G : SobolevSpace (hausdorff n X) hX.quadratic),
      IsWeakLaplacian (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic D) ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic t ht f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht f) ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic G x|≤(L:ℝ)^2) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let U := heatSobolev μ Q t ht f
  let hm := localGamma_memLp_of_bounded_gradient μ Q U U L hL
  let H := hm.toLp (localGamma μ Q U U)
  have hHr : H =ᵐ[μ] localGamma μ Q U U := hm.coeFn_toLp
  have hHs : (fun x => (SobolevSpace.minimalSlope μ Q U x)^2) =ᵐ[μ] H :=
    (localGamma_self μ Q U).symm.trans hHr.symm
  have hHb : ∀ᵐ x ∂μ, |H x|≤(L:ℝ)^2 := by
    filter_upwards [hHs,hL,(Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q U)] with x hx hl hn
    rw [←hx,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hn hl 2
  have hE : energyLp μ H ≠ ∞ := hX.heat_gamma_finite_energy hn p f ht H (L^2) hHs
    (by simpa only [NNReal.coe_pow] using hHb)
  let D := heatSobolevMap μ Q (t/2) (half_pos ht) (-heatGeneratorAt μ Q (t-t/2) f)
  exact ⟨D,⟨H,hE⟩,heatTail_weak_laplacian μ Q t ht f,hHr,hHb⟩

end RegularPointCoordinates

end

end OAI
