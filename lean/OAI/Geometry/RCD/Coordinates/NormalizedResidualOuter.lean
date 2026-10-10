import OAI.Geometry.RCD.Harmonic.LocalResidualOuterBound
import OAI.Geometry.RCD.Coordinates.NormalizedFitEnergy

namespace OAI

/-! # The transport estimate in normalized local L2 spaces -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] hQ in
theorem localL2_norm_eq_root_mul_normalized (s : Set X) (hfin : μ s ≠ ∞)
    (hpos : 0 < μ.real s) (f : Lp ℝ 2 (μ.restrict s)) :
    ‖f‖ = Real.sqrt (μ.real s) * ‖normalizeLocalL2 μ s hfin f‖ := by
  rw [normalizeLocalL2, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, restrictedOne_norm]
  field_simp [(Real.sqrt_pos.mpr hpos).ne']

variable [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ]

/-- The outer normalized norm is bounded uniformly from the inner one.
Only a fixed four-to-one volume ratio is lost in the forcing coefficient. -/
theorem normalized_residual_outer_bound (n : ℕ) {F E W : ℝ}
    (hF : 0 ≤ F) (hW : 0 ≤ W) (C : ℝ≥0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (R a : ℝ), 0 < R → 0 ≤ a → a ≤ (n : ℝ) + 1 →
      ∀ (z : X) (f w q : SobolevSpace μ hQ) (σ : ℝ), 0 ≤ σ →
      IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a →
      ∀ {B : ℝ} (hf : ∀ᵐ x ∂μ.restrict (ball z (4 * R)), localGamma μ hQ f f x ≤ B),
      (∀ᵐ x ∂μ.restrict (ball z (4 * R)), |SobolevSpace.toLp μ hQ w x| ≤ C) →
      ∀ e : X → ℝ, MemLp e 2 μ →
      localRadialDerivative μ hQ (ball z (4 * R)) f hf w =
        SobolevSpace.restrictLp μ hQ (ball z (4 * R)) (w + q) →
      localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) =ᵐ[μ.restrict (ball z (3 * R))]
        (fun x => e x - dist z x) →
      μ (sphere z R) = 0 →
      ∀ (hfin : ∀ t : ℝ, μ (ball z t) ≠ ∞),
      0 < μ.real (ball z R) →
      μ.real (ball z (4 * R)) ≤ W ^ 2 * μ.real (ball z R) →
      ‖normalizeLocalL2 μ (ball z (4 * R)) (hfin _)
        (SobolevSpace.restrictLp μ hQ (ball z (4 * R)) q)‖ ≤
        F * (‖normalizeLocalL2 μ (ball z R) (hfin _)
          (SobolevSpace.restrictLp μ hQ (ball z R) w)‖ + σ) →
      (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) ≤
        E ^ 2 * R ^ 2 * μ.real (ball z R) * σ ^ 2 →
      ‖normalizeLocalL2 μ (ball z (2 * R)) (hfin _)
        (SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w)‖ ≤
        T * (‖normalizeLocalL2 μ (ball z R) (hfin _)
          (SobolevSpace.restrictLp μ hQ (ball z R) w)‖ + σ) := by
  obtain ⟨T, hT, hb⟩ := local_uniform_residual_outer_bound μ hQ n (E := E) (mul_nonneg hF hW) C
  refine ⟨T, hT, ?_⟩
  intro R a hR ha han z f w q σ hσ hlap B hf hw e he heuler hradial hsphere hfin hvol hratio hq herr
  let α := ‖normalizeLocalL2 μ (ball z R) (hfin _)
    (SobolevSpace.restrictLp μ hQ (ball z R) w)‖
  let v := Real.sqrt (μ.real (ball z R))
  let v₂ := Real.sqrt (μ.real (ball z (2 * R)))
  let v₄ := Real.sqrt (μ.real (ball z (4 * R)))
  have hv : 0 < v := Real.sqrt_pos.mpr hvol
  have hvle : v ≤ v₂ := Real.sqrt_le_sqrt
    (measureReal_mono (ball_subset_ball (by linarith)) (hfin _))
  have hvol₂ : 0 < μ.real (ball z (2 * R)) :=
    hvol.trans_le (measureReal_mono (ball_subset_ball (by linarith)) (hfin _))
  have hvol₄ : 0 < μ.real (ball z (4 * R)) :=
    hvol.trans_le (measureReal_mono (ball_subset_ball (by linarith)) (hfin _))
  have hv₄ : v₄ ≤ W * v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hW hv.le)).mp
    dsimp only [v₄, v]
    rw [mul_pow, Real.sq_sqrt hvol.le, Real.sq_sqrt hvol₄.le]
    exact hratio
  have hwraw : ‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ = v * α :=
    localL2_norm_eq_root_mul_normalized μ _ (hfin _) hvol _
  have hqraw : ‖SobolevSpace.restrictLp μ hQ (ball z (4 * R)) q‖ ≤
      (F * W) * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + v * σ) := by
    rw [localL2_norm_eq_root_mul_normalized μ _ (hfin _) hvol₄]
    calc
      _ ≤ v₄ * (F * (α + σ)) := mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
      _ ≤ (W * v) * (F * (α + σ)) := mul_le_mul_of_nonneg_right hv₄
        (mul_nonneg hF (add_nonneg (norm_nonneg _) hσ))
      _ = _ := by rw [hwraw]; ring
  have heraw : (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) ≤ E ^ 2 * R ^ 2 * (v * σ) ^ 2 := by
    rw [mul_pow, show v ^ 2 = μ.real (ball z R) from Real.sq_sqrt hvol.le]
    simpa only [mul_assoc] using herr
  have hout := hb R a hR ha han z f w q (v * σ) (mul_nonneg hv.le hσ)
    hlap hf hw e he heuler hradial hsphere hqraw heraw
  rw [hwraw, localL2_norm_eq_root_mul_normalized μ _ (hfin _) hvol₂] at hout
  have hscaled : v * ‖normalizeLocalL2 μ (ball z (2 * R)) (hfin _)
      (SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w)‖ ≤ v * (T * (α + σ)) := by
    calc
      _ ≤ v₂ * ‖normalizeLocalL2 μ (ball z (2 * R)) (hfin _)
          (SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w)‖ :=
        mul_le_mul_of_nonneg_right hvle (norm_nonneg _)
      _ ≤ _ := hout
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hv).mp hscaled

end RegularPointCoordinates

end

end OAI
