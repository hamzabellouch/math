import OAI.Geometry.RCD.Metric.InwardDistance

namespace OAI

/-! # Changing the outer cutoff radius of the distance primitive -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

omit [IsFiniteMeasureOnCompacts μ] in
theorem localGamma_eq_of_constant_difference (s : Set X)
    (f g a : SobolevSpace μ hQ) (c : ℝ)
    (hfg : SobolevSpace.toLp μ hQ (f - g) =ᵐ[μ.restrict s] fun _ => c) :
    localGamma μ hQ f a =ᵐ[μ.restrict s] localGamma μ hQ g a := by
  filter_upwards [hfg, ae_restrict_of_ae (localGamma_zero_on_level μ hQ (f - g) a c),
    ae_restrict_of_ae (localGamma_sub_left μ hQ f g a)] with x hx hz hs
  have hzero := hz hx
  rw [hs] at hzero
  exact sub_eq_zero.mp hzero

omit [IsFiniteMeasureOnCompacts μ] in
theorem localGamma_self_eq_of_constant_difference (s : Set X)
    (f g : SobolevSpace μ hQ) (c : ℝ)
    (hfg : SobolevSpace.toLp μ hQ (f - g) =ᵐ[μ.restrict s] fun _ => c) :
    localGamma μ hQ f f =ᵐ[μ.restrict s] localGamma μ hQ g g := by
  filter_upwards [localGamma_eq_of_constant_difference μ hQ s f g f c hfg,
    localGamma_eq_of_constant_difference μ hQ s f g g c hfg,
    ae_restrict_of_ae (localGamma_comm μ hQ g f)] with x hf hg hc
  exact hf.trans (hc.trans hg)

theorem inwardSobolev_constant_difference (p : X) {r R : ℝ} (hrR : r ≤ R) :
    SobolevSpace.toLp μ hQ (inwardSobolev μ hQ p R - inwardSobolev μ hQ p r)
      =ᵐ[μ.restrict (ball p r)] fun _ => R - r := by
  filter_upwards [ae_restrict_of_ae (inwardSobolev_coe μ hQ p R),
    ae_restrict_of_ae (inwardSobolev_coe μ hQ p r),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ (inwardSobolev μ hQ p R))
      (SobolevSpace.toLp μ hQ (inwardSobolev μ hQ p r))), ae_restrict_mem measurableSet_ball]
    with x hR hr hsub hx
  have hd : dist p x < r := by simpa only [mem_ball, dist_comm] using hx
  change (SobolevSpace.toLp μ hQ (inwardSobolev μ hQ p R) -
    SobolevSpace.toLp μ hQ (inwardSobolev μ hQ p r)) x = _
  simp only [hsub, Pi.sub_apply, hR, hr, inwardDistance,
    max_eq_left (sub_nonneg.mpr hd.le), max_eq_left (sub_nonneg.mpr (hd.le.trans hrR))]
  ring

theorem inwardSobolev_eikonal_mono (p : X) {r R : ℝ} (hrR : r ≤ R)
    (heik : ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1) :
    ∀ᵐ x ∂μ.restrict (ball p r),
      localGamma μ hQ (inwardSobolev μ hQ p r) (inwardSobolev μ hQ p r) x = 1 := by
  have heq := localGamma_self_eq_of_constant_difference μ hQ (ball p r)
    (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p r) (R - r)
    (inwardSobolev_constant_difference μ hQ p hrR)
  filter_upwards [heq, ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR) heik]
    with x hx he
  exact hx.symm.trans he

end RegularPointCoordinates

end

end OAI
