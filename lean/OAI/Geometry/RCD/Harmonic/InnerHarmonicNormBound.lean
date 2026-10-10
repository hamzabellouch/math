import OAI.Geometry.RCD.Metric.MeasuredAnnularMass
import OAI.Geometry.RCD.Harmonic.HarmonicAffineImprovement
import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Changing the normalization of actual harmonic candidates -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.inner_harmonic_norm_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S R C : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : R≤S) (hC : 0<C)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (hε : Tendsto ε atTop (𝓝 0))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k)‖^2≤
      C*(hausdorff n X).real (ball (p k) (S*r k))) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ k in atTop, harmonicTargetNorm hX (p k) (R*r k) (w k)≤M := by
  let μ := hausdorff n X
  let b := (volume.real (ball (0:Euclidean n) S))⁻¹*volume.real (ball (0:Euclidean n) R)
  have hb : 0<b := mul_pos
    (inv_pos.mpr (ENNReal.toReal_pos (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top))
    (ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' measure_ball_ne_top)
  have hmass := measured_ball_mass_tendsto hS hR hRS hr hV
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) hε
  refine ⟨Real.sqrt (2*C/b),Real.sqrt_pos.mpr (by positivity),?_⟩
  filter_upwards [hmass.eventually (Ioi_mem_nhds (show b/2<b by linarith))] with k hk
  have hmS : 0<μ.real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hmR : 0<μ.real (ball (p k) (R*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hR (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hratio : μ.real (ball (p k) (S*r k))≤(2/b)*μ.real (ball (p k) (R*r k)) := by
    change b/2<(μ.real (ball (p k) (S*r k)))⁻¹*μ.real (ball (p k) (R*r k)) at hk
    rw [← div_eq_inv_mul] at hk
    have hh := (lt_div_iff₀ hmS).mp hk
    have hh' : μ.real (ball (p k) (S*r k))≤(2*μ.real (ball (p k) (R*r k)))/b :=
      (le_div_iff₀ hb).mpr (by nlinarith)
    exact hh'.trans_eq (by ring)
  have hint : (∫ x in ball (p k) (R*r k),
      (SobolevSpace.toLp μ hX.quadratic (w k) x)^2 ∂μ)≤
      ‖SobolevSpace.toLp μ hX.quadratic (w k)‖^2 := by
    rw [← lp_integral_square_eq_norm_square]
    exact setIntegral_le_integral (Lp.memLp _).integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hsq := normalized_sobolev_mean_sq μ hX.quadratic (ball (p k) (R*r k))
    (hX.finiteOnBounded _ isBounded_ball).ne (w k)
  change harmonicTargetNorm hX (p k) (R*r k) (w k)^2=_ at hsq
  have hi : (∫ x in ball (p k) (R*r k),
      (SobolevSpace.toLp μ hX.quadratic (w k) x)^2 ∂μ)≤
      (2*C/b)*μ.real (ball (p k) (R*r k)) := by
    have hh := mul_le_mul_of_nonneg_left hratio hC.le
    have hu := hint.trans (hw k)
    calc _ ≤ C*μ.real (ball (p k) (S*r k)) := hu
         _ ≤ _ := by convert hh using 1; ring
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  change harmonicTargetNorm hX (p k) (R*r k) (w k)^2≤(Real.sqrt (2*C/b))^2
  rw [Real.sq_sqrt (by positivity),hsq]
  have hh := mul_le_mul_of_nonneg_left hi (inv_pos.mpr hmR).le
  convert hh using 1
  field_simp

end RegularPointCoordinates

end

end OAI
