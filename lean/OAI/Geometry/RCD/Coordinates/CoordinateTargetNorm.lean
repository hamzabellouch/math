import OAI.Geometry.RCD.Coordinates.HarmonicCoordinateValueLimit

namespace OAI

/-! # Actual coordinate limits give uniform interior normalization bounds -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.target_norm_le_of_pointwise {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p : X} {R B : ℝ} (hR : 0<R) (hB : 0≤B)
    (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤B) :
    harmonicTargetNorm hX p R u≤B := by
  let μ := hausdorff n X
  have : IsFiniteMeasure (μ.restrict (ball p R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (ball p R) isBounded_ball⟩
  have hm : 0<μ.real (ball p R) :=
    ENNReal.toReal_pos (hX.fullSupport p R hR).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hi := integral_mono_ae (Lp.memLp (SobolevSpace.toLp μ hX.quadratic u)).integrable_sq.restrict
    (integrable_const (B^2)) (hu.mono fun x hx => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2)
  have hi' : (∫ x in ball p R, (SobolevSpace.toLp μ hX.quadratic u x)^2 ∂μ)≤
      B^2*μ.real (ball p R) := by
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hi
  apply (sq_le_sq₀ (norm_nonneg _) hB).mp
  change harmonicTargetNorm hX p R u^2≤B^2
  rw [show harmonicTargetNorm hX p R u^2=_ from
    normalized_sobolev_mean_sq μ hX.quadratic (ball p R) (hX.finiteOnBounded _ isBounded_ball).ne u]
  calc _ ≤ (μ.real (ball p R))⁻¹*(B^2*μ.real (ball p R)) :=
          mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr hm.le)
       _ = B^2 := by field_simp

omit [ProperSpace X] in
theorem NoncollapsedRCD.coordinate_target_norm_eventually {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S W : ℝ} (hW : 0<W) (hWS : W≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic) (i : Fin n)
    (hconv : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-V k x i|≤1) :
    ∀ᶠ k in atTop, harmonicTargetNorm hX (p k) (W*r k) (u k)≤W+2 := by
  filter_upwards [hconv,hεlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))]
    with k hk hεk
  apply hX.target_norm_le_of_pointwise (mul_pos hW (hr k)) (by linarith) (u k)
  filter_upwards [hk,self_mem_ae_restrict measurableSet_ball] with x hx hxb
  have hnorm := (abs_le.mp (pointed_radial_distance (hr k) (hW.le.trans hWS) (hV k).metric
    (hxb.le.trans (mul_le_mul_of_nonneg_right hWS (hr k).le)))).2
  have hdist : dist x (p k)/r k<W := (div_lt_iff₀ (hr k)).mpr hxb
  have hi : |V k x i|≤‖V k x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (V k x) i
  calc _ = |(SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-V k x i)+V k x i| := by congr 1; ring
       _ ≤ |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-V k x i|+|V k x i| := abs_add_le _ _
       _ ≤ W+2 := by linarith

end RegularPointCoordinates

end

end OAI
