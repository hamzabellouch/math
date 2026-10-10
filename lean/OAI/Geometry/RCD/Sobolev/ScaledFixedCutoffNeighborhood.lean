import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.ScaledCutoffL1
import OAI.Geometry.RCD.Sobolev.ScaledUniformCutoff

namespace OAI

/-! # A regular-neighborhood cutoff with a uniform starting index -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

private theorem half_volume_upper {n : ℕ} {v omega s : ℝ} (hw : 0 < omega) (hs : 0 < s)
    (h : |v / (omega * s ^ n) - 1| ≤ 1 / 2) : v ≤ (3 / 2 * omega) * s ^ n := by
  have hd : 0 < omega * s ^ n := mul_pos hw (pow_pos hs n)
  have hb := (abs_le.mp h).2
  have hq : v / (omega * s ^ n) ≤ 3 / 2 := by linarith
  have hm := (div_le_iff₀ hd).mp hq
  nlinarith only [hm]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The cutoff constant and starting index are fixed before the radius,
coordinate map or full Bochner measure is chosen. Only local
calculus and the displayed regular-neighborhood volume bounds are used. -/
theorem exists_scaled_fixed_cutoff_neighborhood_with_source {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2 ≤ n)
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    (hcutoff : LocalGoodCutoffInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) {omega : ℝ} (homega : 0 < omega) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      (∀ p s, 0 < s → -1 ≤ K * s ^ 2 →
        Nonempty (GoodLaplacianCutoff (hausdorff n X) hX.quadratic p s C)) ∧
      ∃ J : ℕ, ∀ (R : ℝ), 0 < R → R ≤ 1 →
      |K| * (16 * R) ^ 2 ≤ 1 → ∀ (p : X) (L : ℝ≥0)
      (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
      (M : PositiveBilinearMeasure X (Euclidean n)),
      (L : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 →
      (∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (32 * R)) (u i)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (32 * R)),
        localGamma (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u v)
          (sobolevColumnMap (hausdorff n X) hX.quadratic u v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      (∀ y, dist p y ≤ 16 * R → ∀ s, 0 < s → s ≤ 32 * R →
        |(hausdorff n X).real (ball y s) / (omega * s ^ n) - 1| ≤ 1 / 2) →
      ∀ G : ∀ v, LocalHarmonicEnergy (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u) M |K| p (4 * R) L v,
      ∃ χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 8) C,
      (∀ w : Euclidean n, ‖w‖ ≤ 2 → R ^ 2 *
        (∫ z, |cutoffSourceDensity (hausdorff n X) hX.quadratic
          (G w).energy χ.sobolev χ.laplacian z| ∂hausdorff n X) ≤ A * R ^ n) ∧
      ∀ q ∈ ball p (R / 32),
        (∀ x ∈ ball q (R / 4), (χ.weight : X → ℝ) x = 1) ∧
        (∀ x ∉ ball q R, (χ.weight : X → ℝ) x = 0) ∧
        ∀ i, J ≤ i → ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          ‖harmonicHeatError (hausdorff n X) hX.quadratic (k := ker) G χ t q‖ ≤ (R ^ 2)⁻¹ := by
  let μ := hausdorff n X
  obtain ⟨C, hC, hcut⟩ := hcutoff hn
  let B := 4 * (n : ℝ) ^ 2
  let D := 4 * B
  let V := 3 / 2 * omega
  let A := (64 * (D * C + C ^ 2) + 4 * D ^ 2 * (C / 2 + 1) * 3 ^ n) * V
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hA : 0 ≤ A := by dsimp only [A, D]; positivity
  obtain ⟨J, hJ⟩ := exists_scaled_cutoff_error_index μ hX.quadratic hk n hg hA
    (show 0 < omega / 2 by positivity)
  refine ⟨C, A, hC, hA, hcut, J, ?_⟩
  intro R hR hR1 hcurv p L u M hL hu hgrad hvolume G
  have hcurvR : |K| * R ^ 2 ≤ 1 := by
    have h := mul_nonneg (abs_nonneg K) (sq_nonneg R)
    nlinarith
  have hKR : -1 ≤ K * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg R)
    linarith
  have hKρ : -1 ≤ K * (3 * R / 8) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (3 * R / 8))
    nlinarith
  obtain ⟨χ⟩ := hcut p (3 * R / 8) (by positivity) hKρ
  obtain ⟨ψ⟩ := hcut p R hR hKR
  have hvR : μ.real (ball p R) ≤ V * R ^ n :=
    half_volume_upper homega hR (hvolume p (by simp; positivity) R hR (by linarith))
  have hv2R : μ.real (closedBall p (2 * R)) ≤ V * (3 * R) ^ n := by
    apply (measureReal_mono (closedBall_subset_ball (show 2 * R < 3 * R by linarith))
      (hX.finiteOnBounded _ isBounded_ball).ne).trans
    exact half_volume_upper homega (by positivity)
      (hvolume p (by simp; positivity) (3 * R) (by positivity) (by linarith))
  have hsource (v : Euclidean n) (hv : ‖v‖ ≤ 2) :
      R ^ 2 * (∫ z, |cutoffSourceDensity μ hX.quadratic
        (G v).energy χ.sobolev χ.laplacian z| ∂μ) ≤ A * R ^ n :=
    harmonic_cutoff_uniform_L1 hX hhessian hproduct hR (abs_nonneg K) (neg_abs_le K)
      hcurvR hC0 hV hB L u hu hgrad G χ ψ hvR hv2R v hL hv
  have hvolLower : ∀ y, 3 * R / 8 ≤ dist p y → dist p y ≤ 3 * R / 4 →
      ∀ s, 0 < s → s ≤ R → (omega / 2) * s ^ n ≤ μ.real (ball y s) := by
    intro y _hy hy s hs hsR
    have hb := (abs_le.mp (hvolume y (by linarith) s hs (by linarith))).1
    have hd : 0 < omega * s ^ n := mul_pos homega (pow_pos hs n)
    have hq : 1 / 2 ≤ μ.real (ball y s) / (omega * s ^ n) := by linarith
    have hm := (le_div_iff₀ hd).mp hq
    nlinarith only [hm]
  refine ⟨χ, hsource, ?_⟩
  intro q hq
  have hqp : dist q p < R / 32 := hq
  refine ⟨?_, ?_, hJ R hR hR1 p (4 * R) |K| C L _ M G χ hsource hvolLower q hq⟩
  · intro x hx
    apply χ.one
    have hxq : dist x q < R / 4 := hx
    change dist x p < 3 * R / 8
    linarith [dist_triangle x q p]
  · intro x hx
    apply χ.zero
    have hxq : R ≤ dist x q := by simpa only [mem_ball, not_lt] using hx
    have ht := dist_triangle x p q
    rw [dist_comm p q] at ht
    rw [dist_comm p x]
    linarith

/-- The cutoff constant and starting index are fixed before the radius,
coordinate map or full Bochner measure is chosen. Only local
calculus and the displayed regular-neighborhood volume bounds are used. -/
theorem exists_scaled_fixed_cutoff_neighborhood {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2 ≤ n)
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    (hcutoff : LocalGoodCutoffInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) {omega : ℝ} (homega : 0 < omega) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ J : ℕ, ∀ (R : ℝ), 0 < R → R ≤ 1 →
      |K| * (16 * R) ^ 2 ≤ 1 → ∀ (p : X) (L : ℝ≥0)
      (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
      (M : PositiveBilinearMeasure X (Euclidean n)),
      (L : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 →
      (∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (32 * R)) (u i)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (32 * R)),
        localGamma (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u v)
          (sobolevColumnMap (hausdorff n X) hX.quadratic u v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      (∀ y, dist p y ≤ 16 * R → ∀ s, 0 < s → s ≤ 32 * R →
        |(hausdorff n X).real (ball y s) / (omega * s ^ n) - 1| ≤ 1 / 2) →
      ∀ G : ∀ v, LocalHarmonicEnergy (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u) M |K| p (4 * R) L v,
      ∃ χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 8) C,
      ∀ q ∈ ball p (R / 32),
        (∀ x ∈ ball q (R / 4), (χ.weight : X → ℝ) x = 1) ∧
        (∀ x ∉ ball q R, (χ.weight : X → ℝ) x = 0) ∧
        ∀ i, J ≤ i → ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          ‖harmonicHeatError (hausdorff n X) hX.quadratic (k := ker) G χ t q‖ ≤ (R ^ 2)⁻¹ := by
  obtain ⟨C, A, hC, _hA, _hcut, J, h⟩ :=
    exists_scaled_fixed_cutoff_neighborhood_with_source hX hn hhessian hproduct hcutoff hk hg homega
  refine ⟨C, hC, J, ?_⟩
  intro R hR hR1 hcurv p L u M hL hu hgrad hvolume G
  obtain ⟨χ, _, hχ⟩ := h R hR hR1 hcurv p L u M hL hu hgrad hvolume G
  exact ⟨χ, hχ⟩

end RegularPointCoordinates

end

end OAI
