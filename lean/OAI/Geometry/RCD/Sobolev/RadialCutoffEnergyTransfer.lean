import OAI.Geometry.RCD.Sobolev.MeasuredRadialCutoffSupport
import OAI.Geometry.RCD.Coordinates.NormalizedUniformMean
import OAI.Geometry.RCD.Sobolev.HarmonicScaledEnergy

namespace OAI

/-! # Replacing a physical radial cutoff by its Euclidean image weight

Only an interior gradient bound is used. Both cutoffs vanish outside that
interior ball once the measured-approximation error is small.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.radial_cutoff_energy_error_tendsto {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S a b R M : ℝ} (hS : 0<S) (hab : a<b)
    (hbR : b<R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k),
        ((nestedBallCutoff (p k) (a*r k) (b*r k) x)^2-(euclideanNestedCutoff n hab (V k x))^2)*
          localGamma (hausdorff n X) hX.quadratic (w k) (w k) x ∂hausdorff n X)
      atTop (𝓝 0) := by
  let μ := hausdorff n X
  let U := fun k => ball (p k) (S*r k)
  let z := fun k x => (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2-
    (euclideanNestedCutoff n hab (V k x))^2
  let F := fun k x => z k x*(r k^2*localGamma μ hX.quadratic (w k) (w k) x)
  let : ∀ k, IsFiniteMeasure (μ.restrict (U k)) := fun k => ⟨by
    simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (U k) isBounded_ball⟩
  have hmass (k : ℕ) : 0<(μ.restrict (U k)).real univ := by
    simp only [Measure.real,Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hrate : Tendsto (fun k => 4*ε k/(b-a)*M) atTop (𝓝 0) := by
    convert ((hεlim.const_mul 4).div_const (b-a)).mul_const M using 1
    simp
  have hsmall : ∀ᶠ k in atTop, 2*ε k<R-b := by
    have hh := (hεlim.const_mul 2).eventually (Iio_mem_nhds (show 2*(0:ℝ)<R-b by simpa only [mul_zero] using sub_pos.mpr hbR))
    simpa only [mul_zero] using hh
  have hmean := normalized_mean_tendsto_zero (fun k => μ.restrict (U k)) hmass F (by
    intro δ hδ
    filter_upwards [hw,hsmall,hrate.eventually (Iio_mem_nhds hδ)] with k hwk hsk hrk
    have hcond := (ae_restrict_iff' measurableSet_ball).mp hwk
    filter_upwards [ae_restrict_of_ae hcond,ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (localGamma_self μ hX.quadratic (w k))] with x hwx hx hself
    change x∈ball (p k) (S*r k) at hx
    by_cases hxR : x∈ball (p k) (R*r k)
    · have hγn : 0≤r k^2*localGamma μ hX.quadratic (w k) (w k) x :=
        mul_nonneg (sq_nonneg _) (hself ▸ sq_nonneg _)
      have hz := measured_radial_cutoff_square_error (hr k) hS.le hab (hV k).metric hx.le
      have hh := mul_le_mul hz (hwx hxR) hγn (by
        have hε : 0≤ε k := dist_nonneg.trans (hV k).metric.1
        exact div_nonneg (mul_nonneg (by norm_num) hε) (sub_pos.mpr hab).le)
      change |z k x*(r k^2*localGamma μ hX.quadratic (w k) (w k) x)|≤δ
      rw [abs_mul,abs_of_nonneg hγn]
      exact hh.trans hrk.le
    · have hz := measured_radial_cutoff_zero_outside (hr k) hS.le hab hsk (hV k).metric hx.le hxR
      simp only [F,z,hz.1,hz.2,zero_pow (by decide : 2≠0),sub_self,zero_mul,abs_zero]
      exact hδ.le)
  convert hmean using 1
  funext k
  simp only [Measure.real,Measure.restrict_apply_univ]
  have he : F k=fun x => r k^2*(z k x*localGamma μ hX.quadratic (w k) (w k) x) := by
    funext x
    dsimp only [F]
    ring
  rw [he,integral_const_mul]
  dsimp only [z,U,μ]
  ring

end RegularPointCoordinates

end

end OAI
