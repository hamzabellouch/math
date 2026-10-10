import OAI.Geometry.RCD.Coordinates.WeightedFramedProjection
import OAI.Geometry.RCD.Sobolev.ProjectedEulerIdentity

namespace OAI

/-! # The actual affine residual and its scale-correct Euler forcing -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The physical value bound and the radius-weighted affine estimate
control the actual projection coefficients. Subtracting that same fit
preserves harmonicity and gives a forcing of order `R² * σ`. -/
theorem physical_projection_euler {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s Ω : Set X) (hfin : μ s ≠ ∞)
    (hfinΩ : μ Ω ≠ ∞) (hsΩ : s ⊆ Ω) (hΩ : MeasurableSet Ω)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (f v η ev : SobolevSpace μ hQ) (hv : IsSobolevHarmonicOn μ hQ Ω v)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (N : Euclidean n ≃L[ℝ] Euclidean n) {R H V E D σ B : ℝ}
    (_hR : 0 < R) (hH : 0 ≤ H) (_hV : 0 ≤ V) (_hE : 0 ≤ E)
    (hD : 0 ≤ D) (hσ : 0 ≤ σ)
    (hbound : ∀ c a, |c| + R * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 μ s hfin (affineCoordinateMap μ hQ u s hfin (c, a))‖)
    (hvalue : ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s v)‖ ≤ V * R ^ 2)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (G : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (A : Euclidean n →L[ℝ] Euclidean n) (k : ℝ)
    (hEuler : localRadialDerivative μ hQ Ω f hf v =
      SobolevSpace.restrictLp μ hQ Ω (v + k • η + ev))
    (hG : ∀ a, localRadialDerivative μ hQ Ω f hf
      (sobolevColumnMap μ hQ u a) = SobolevSpace.restrictLp μ hQ Ω (G a))
    (hev : ‖normalizeLocalL2 μ Ω hfinΩ (SobolevSpace.restrictLp μ hQ Ω ev)‖ ≤ E * R ^ 2 * σ)
    (hfit : ∀ b, ‖normalizeLocalL2 μ Ω hfinΩ (SobolevSpace.restrictLp μ hQ Ω
      (G (N b) - sobolevColumnMap μ hQ u (A (N b))))‖ ≤ D * R * ‖b‖ * σ) :
    ∃ (c : ℝ) (b : Euclidean n),
      let w := v - c • η - sobolevColumnMap μ hQ u (N b)
      let e := ev - (G (N b) - sobolevColumnMap μ hQ u (A (N b)))
      IsSobolevHarmonicOn μ hQ Ω w ∧
      SobolevSpace.restrictLp μ hQ s w = affineResidual μ hQ u s hfin
        (SobolevSpace.restrictLp μ hQ s v) ∧
      |c| + R * ‖b‖ ≤ H * V * R ^ 2 ∧
      localRadialDerivative μ hQ Ω f hf w = SobolevSpace.restrictLp μ hQ Ω
        (w + sobolevColumnMap μ hQ u (N b - A (N b)) + (k + c) • η + e) ∧
      ‖normalizeLocalL2 μ Ω hfinΩ (SobolevSpace.restrictLp μ hQ Ω e)‖ ≤
        (E + D * H * V) * R ^ 2 * σ := by
  obtain ⟨c, b, w, hw, hharm, hproj, hcb⟩ := weighted_framed_harmonic_projection_residual
    μ hQ u s Ω hfin hsΩ hΩ hu v η hv hη N R hH hbound
  have hw' : w = v - c • η - sobolevColumnMap μ hQ u (N b) := by rw [hw]; module
  rw [hw'] at hharm hproj
  have hcb' : |c| + R * ‖b‖ ≤ H * V * R ^ 2 :=
    hcb.trans ((mul_le_mul_of_nonneg_left hvalue hH).trans_eq (by ring))
  refine ⟨c, b, hharm, hproj, hcb', ?_, ?_⟩
  · exact projected_euler_identity μ hQ Ω f v η ev hf hη
      (sobolevColumnMap μ hQ u) G A (N b) k c hEuler (hG (N b))
  · have he : ‖normalizeLocalL2 μ Ω hfinΩ (SobolevSpace.restrictLp μ hQ Ω
        (ev - (G (N b) - sobolevColumnMap μ hQ u (A (N b)))))‖ ≤
          E * R ^ 2 * σ + D * R * ‖b‖ * σ := by
      rw [map_sub]
      simpa only [normalizeLocalL2, smul_sub] using
        (norm_sub_le (normalizeLocalL2 μ Ω hfinΩ (SobolevSpace.restrictLp μ hQ Ω ev))
          (normalizeLocalL2 μ Ω hfinΩ (SobolevSpace.restrictLp μ hQ Ω
            (G (N b) - sobolevColumnMap μ hQ u (A (N b)))))).trans (add_le_add hev (hfit b))
    have hcoef : R * ‖b‖ ≤ H * V * R ^ 2 := (le_add_of_nonneg_left (abs_nonneg c)).trans hcb'
    have hscale := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hD hσ)
    calc
      _ ≤ E * R ^ 2 * σ + D * R * ‖b‖ * σ := he
      _ ≤ (E + D * H * V) * R ^ 2 * σ := by nlinarith only [hscale]

end RegularPointCoordinates

end

end OAI
