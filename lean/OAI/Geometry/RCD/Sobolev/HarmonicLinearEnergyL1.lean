import OAI.Geometry.RCD.Harmonic.HarmonicLinearWeightedDefect
import OAI.Geometry.RCD.Harmonic.WeightedCoreConvergence
import OAI.Geometry.RCD.Metric.MeasuredAnnularMass
import OAI.Geometry.RCD.Sobolev.MeasuredRadialCutoff

namespace OAI

/-! # L1 convergence of the actual harmonic energy on the original inner ball -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_linear_energy_l1 {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*r k^2) (hcurv5 : ∀ k, -1≤K*(5*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0<M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k)≤M)
    (L : Euclidean n →L[ℝ] ℝ) (hL : ‖L‖=1)
    (hconv : ∀ W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-L (V k x)|≤δ) :
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x-1|
        ∂hausdorff n X) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Ω := fun k => ball (p k) (5*r k)
  let A := fun k => ball (p k) (2*r k)
  let mass := fun k => μ.real (Ω k)
  let φ : Euclidean n →ᵇ ℝ := euclideanNestedCutoff n (a:=9/4) (b:=5/2) (by norm_num)
  have hφ (z : Euclidean n) : 0≤φ z := (nestedBallCutoff_bounds 0 (9/4) (5/2) z).1
  have hφ1 (z : Euclidean n) : φ z≤1 := (nestedBallCutoff_bounds 0 (9/4) (5/2) z).2
  have hs : Function.support φ⊆ball 0 (11/4) := by
    intro z hz
    by_contra ht
    have hdist : 5/2≤dist (0:Euclidean n) z := by
      have hh : 11/4≤dist z (0:Euclidean n) := le_of_not_gt ht
      rw [dist_comm]
      linarith
    exact hz (nestedBallCutoff_eq_zero 0 (by norm_num : (9/4:ℝ)<5/2) hdist)
  have hlim := hX.harmonic_linear_weighted_defect hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
    w hw hM hnorm L hL hconv φ hφ hφ1 hs
  let f := fun k x => φ (V k x)
  let e := fun k x => |r k^2*localGamma μ hX.quadratic (w k) (w k) x-1|
  have hfinite (k : ℕ) : μ (Ω k)≠⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hm (k : ℕ) : 0 < mass k := ENNReal.toReal_pos
    (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne' (hfinite k)
  have he (k : ℕ) : IntegrableOn (e k) (Ω k) μ :=
    (((localGamma_memL1 μ hX.quadratic (w k) (w k)).const_mul (r k^2)).integrableOn.sub
      (integrableOn_const (hfinite k))).abs
  have hfe (k : ℕ) : IntegrableOn (fun x => f k x*e k x) (Ω k) μ :=
    (he k).bdd_mul ((φ.continuous.measurable.comp (hV k).measurable).aestronglyMeasurable.restrict)
      (Eventually.of_forall (fun x => φ.norm_coe_le_norm (V k x)))
  have hsub (k : ℕ) : A k⊆Ω k :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤5) (hr k).le)
  have hp : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (A k), f k x=1 := by
    filter_upwards [hεlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/8))] with k hk
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
    have hradius := (abs_le.mp (pointed_radial_distance (hr k) (by norm_num : (0:ℝ)≤5)
      (hV k).metric (hsub k hx).le)).2
    have hd : dist x (p k)/r k<2 := (div_lt_iff₀ (hr k)).mpr hx
    apply nestedBallCutoff_eq_one 0 (by norm_num : (9/4:ℝ)<5/2)
    rw [dist_zero_left]
    linarith
  have hmass := measured_ball_mass_tendsto (by norm_num : (0:ℝ)<5) (by norm_num : (0:ℝ)<2)
    (by norm_num) hr hV hfinite hm hεlim
  have hv : (volume.real (ball (0:Euclidean n) 5))⁻¹*volume.real (ball (0:Euclidean n) 2)≠0 := by
    apply ne_of_gt
    exact mul_pos (inv_pos.mpr (ENNReal.toReal_pos (measure_ball_pos volume 0 (by norm_num)).ne'
      measure_ball_lt_top.ne))
      (ENNReal.toReal_pos (measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne)
  exact normalized_weighted_core_convergence μ A Ω (fun k => (mass k)⁻¹)
    (fun k => inv_pos.mpr (hm k)) f e hfe
    (fun _ => Eventually.of_forall (fun _ => abs_nonneg _))
    (fun _ => Eventually.of_forall (fun _ => hφ _)) hsub hp hv hmass hlim

end RegularPointCoordinates

end

end OAI
