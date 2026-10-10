import OAI.Geometry.RCD.Harmonic.BoundedHarmonicCompactness

namespace OAI

/-! # Identifying a prescribed bounded harmonic value limit -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_harmonic_value_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {S M : ℝ} (hS : 0 < S) (hM : 0 < M)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*(r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k) ≤ M)
    (f : Euclidean n → ℝ) (hfc : ContinuousOn f (ball 0 S))
    (hfL : ∀ W < S, ∃ L : ℝ≥0, LipschitzOnWith L f (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0 < W → W < S → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-f (V k x)| ≤ η) :
    InnerProductSpace.HarmonicOnNhd f (ball 0 S) := by
  let μ := hausdorff n X
  let u := fun k => M⁻¹ • w k
  let g := fun z => M⁻¹*f z
  have hunorm (k : ℕ) : harmonicTargetNorm hX (p k) (S*r k) (u k) ≤ 1 := by
    rw [harmonicTargetNorm_smul,abs_of_pos (inv_pos.mpr hM)]
    exact (mul_le_mul_of_nonneg_left (hnorm k) (inv_pos.mpr hM).le).trans_eq
      (inv_mul_cancel₀ hM.ne')
  have hgL : ∀ W < S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W) := by
    intro W hW
    obtain ⟨L,hL⟩ := hfL W hW
    refine ⟨⟨M⁻¹,(inv_pos.mpr hM).le⟩*L,LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    have hh := mul_le_mul_of_nonneg_left (hL.dist_le_mul x hx y hy) (inv_pos.mpr hM).le
    change |M⁻¹*f x-M⁻¹*f y| ≤ (M⁻¹*(L : ℝ))*dist x y
    rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hM)]
    simpa only [Real.dist_eq,mul_assoc] using hh
  have huconv : ∀ W : ℝ, 0 < W → W < S → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hX.quadratic (u k) x-g (V k x)| ≤ η := by
    intro W hW hWS η hη
    filter_upwards [hconv W hW hWS (η*M) (mul_pos hη hM)] with k hk
    have he : SobolevSpace.toLp μ hX.quadratic (u k) =ᵐ[μ]
        fun x => M⁻¹*SobolevSpace.toLp μ hX.quadratic (w k) x := by
      dsimp only [u]
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    filter_upwards [hk,ae_restrict_of_ae he] with x hx heq
    rw [heq]
    change |M⁻¹*SobolevSpace.toLp μ hX.quadratic (w k) x-M⁻¹*f (V k x)| ≤ η
    rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hM)]
    have hh := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hM).le
    exact hh.trans_eq (by field_simp)
  have hgweak := hX.harmonic_value_limit_weak_of_curvature hn hS p r ε hr hcurv hε hε1 hεlim
    V u hV (fun k => (hw k).smul μ hX.quadratic M⁻¹) hunorm g hgL huconv
  have hfweak : EuclideanWeakHarmonicOn f S := by
    intro ψ hψ
    have hh := hgweak ψ hψ
    change (∫ z, (M⁻¹*f z)*_)=0 at hh
    simp_rw [mul_assoc] at hh
    rw [integral_const_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hM.ne')
  exact continuous_weak_harmonic hfc hfweak

end RegularPointCoordinates

end

end OAI
