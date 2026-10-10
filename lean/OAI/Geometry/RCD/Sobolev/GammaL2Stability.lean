import OAI.Geometry.RCD.Sobolev.GammaSquareDifference

namespace OAI

/-! # Strong L² stability of bounded-gradient energy densities -/

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem gammaL2_sub_norm_le (f g : SobolevSpace μ hQ) (L M : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x ≤ M)
    (hff : MemLp (localGamma μ hQ f f) 2 μ) (hgg : MemLp (localGamma μ hQ g g) 2 μ) :
    ‖hff.toLp (localGamma μ hQ f f) - hgg.toLp (localGamma μ hQ g g)‖ ≤
      ((L : ℝ) + M) * ‖f - g‖ := by
  have hh : ‖hff.toLp (localGamma μ hQ f f) - hgg.toLp (localGamma μ hQ g g)‖ ≤
      ((L : ℝ) + M) * ‖SobolevSpace.minimalSlope μ hQ (f - g)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [localGamma_self_sub_bound μ hQ f g L M hf hg,
      hff.coeFn_toLp, hgg.coeFn_toLp,
      Lp.coeFn_sub (hff.toLp (localGamma μ hQ f f)) (hgg.toLp (localGamma μ hQ g g)),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (f - g))]
      with x hx hfx hgx hsub h0
    simpa only [hsub, Pi.sub_apply, hfx, hgx, Real.norm_eq_abs, abs_of_nonneg h0] using hx
  exact hh.trans (mul_le_mul_of_nonneg_left (SobolevSpace.minimalSlope_norm_le μ hQ (f - g))
    (add_nonneg L.coe_nonneg M.coe_nonneg))

/-- Strong Sobolev convergence and a common gradient bound give strong
L² convergence of the actual energy densities. -/
theorem gammaL2_tendsto {u : ℕ → SobolevSpace μ hQ} {f : SobolevSpace μ hQ}
    (L : ℝ≥0)
    (hu : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (u k) x ≤ L)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hconv : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun k => (localGamma_memLp_of_bounded_gradient μ hQ (u k) (u k) L (hu k)).toLp
      (localGamma μ hQ (u k) (u k))) atTop
      (𝓝 ((localGamma_memLp_of_bounded_gradient μ hQ f f L hf).toLp (localGamma μ hQ f f))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => gammaL2_sub_norm_le μ hQ (u k) f L L (hu k) hf _ _)
  have hh := ((hconv.sub (tendsto_const_nhds (x := f))).norm).const_mul ((L : ℝ) + L)
  simpa only [sub_self, norm_zero, mul_zero] using hh

end RegularPointCoordinates

end OAI
