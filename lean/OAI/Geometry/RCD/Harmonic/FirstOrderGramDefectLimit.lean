import OAI.Geometry.RCD.Harmonic.FirstOrderVelocityErrorLimit

namespace OAI

/-! # Vanishing normalized Gram error on the physical working balls -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.first_order_gram_defect_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k)) :
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (4*r k)))⁻¹*
      ∫ z in ball (p k) (4*r k), gramDefect (hausdorff n X) hX.quadratic (u k) z
        ∂hausdorff n X) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨D,_hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1)
  have hpos (k : ℕ) (a : ℝ) (ha : 0<a) : 0<μ.real (ball (p k) (a*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos ha (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  apply squeeze_zero (fun k => mul_nonneg (inv_nonneg.mpr (hpos k 4 (by norm_num)).le)
    (integral_nonneg (gramDefect_nonneg μ Q (u k))))
    (g := fun k => ((n:ℝ)^2*D)*ε k)
  · intro k
    have hv : μ.real (ball (p k) (16*r k))≤D*μ.real (ball (p k) (4*r k)) := by
      have hh := hvol (p k) (16*r k) (mul_pos (by norm_num) (hr k)) (hcurv k) (p k)
        (by simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤16) (hr k).le)
      simpa only [show (1/4:ℝ)*(16*r k)=4*r k by ring] using hh
    have hi := gramDefect_integrableOn μ Q (u k) (hX.finiteOnBounded (ball (p k) (16*r k)) isBounded_ball).ne
    have hb := (setIntegral_mono_set hi (Eventually.of_forall (gramDefect_nonneg μ Q (u k)))
      (Eventually.of_forall (ball_subset_ball (by linarith [hr k] : 4*r k≤16*r k)))).trans
      (gramDefect_integral_bound μ Q (hpos k 16 (by norm_num))
        (hX.finiteOnBounded _ isBounded_ball).ne (hsplit k))
    rw [← div_eq_inv_mul,div_le_iff₀ (hpos k 4 (by norm_num))]
    have hh := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg (n:ℝ)) (hε k))
    exact hb.trans (by convert hh using 1; ring)
  · simpa only [mul_zero] using hε0.const_mul ((n:ℝ)^2*D)

end RegularPointCoordinates

end

end OAI
