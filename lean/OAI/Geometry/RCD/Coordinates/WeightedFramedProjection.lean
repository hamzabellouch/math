import OAI.Geometry.RCD.Coordinates.FramedAffineProjection

namespace OAI

/-! # Radius-weighted coefficients of the actual harmonic projection -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Projection coefficients are bounded in the exact normalization frame;
no bound for the original coordinate change or its inverse is lost. -/
theorem weighted_framed_affine_projection_coefficients {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (R : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ c a, |c| + R * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 μ s hfin (affineCoordinateMap μ hQ u s hfin (c, a))‖)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ∃ (c : ℝ) (b : Euclidean n),
      affineProjection μ hQ u s hfin f = affineCoordinateMap μ hQ u s hfin (c, N b) ∧
      |c| + R * ‖b‖ ≤ H * ‖normalizeLocalL2 μ s hfin f‖ := by
  obtain ⟨c, a, hfit⟩ := affineProjection_has_coefficients μ hQ u s hfin f
  change affineProjection μ hQ u s hfin f = affineCoordinateMap μ hQ u s hfin (c, a) at hfit
  refine ⟨c, N.symm a, by simpa only [N.apply_symm_apply] using hfit, ?_⟩
  have hb := hbound c a
  rw [← hfit] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (normalized_affineProjection_norm_le μ hQ u s hfin f) hH)

variable [BorelSpace X] [ProperSpace X]

/-- The least-squares residual is an actual harmonic Sobolev function on
the larger working set and equals the orthogonal residual on its inner
projection set. Its coefficients satisfy the exact-frame value bound. -/
theorem weighted_framed_harmonic_projection_residual {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s Ω : Set X) (hfin : μ s ≠ ∞)
    (hsΩ : s ⊆ Ω) (hΩ : MeasurableSet Ω)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (v η : SobolevSpace μ hQ) (hv : IsSobolevHarmonicOn μ hQ Ω v)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (N : Euclidean n ≃L[ℝ] Euclidean n) (R : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ c a, |c| + R * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 μ s hfin (affineCoordinateMap μ hQ u s hfin (c, a))‖) :
    ∃ (c : ℝ) (b : Euclidean n) (w : SobolevSpace μ hQ),
      w = v - (c • η + sobolevColumnMap μ hQ u (N b)) ∧
      IsSobolevHarmonicOn μ hQ Ω w ∧
      SobolevSpace.restrictLp μ hQ s w = affineResidual μ hQ u s hfin
        (SobolevSpace.restrictLp μ hQ s v) ∧
      |c| + R * ‖b‖ ≤ H * ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s v)‖ := by
  obtain ⟨c, b, hfit, hb⟩ := weighted_framed_affine_projection_coefficients μ hQ u s hfin N R hH hbound
    (SobolevSpace.restrictLp μ hQ s v)
  let w := v - (c • η + sobolevColumnMap μ hQ u (N b))
  have hηharm := isSobolevHarmonicOn_of_local_constant μ hQ Ω hΩ η 1 hη
  have hwharm : IsSobolevHarmonicOn μ hQ Ω w := by
    have haff := (hηharm.smul μ hQ c).add μ hQ
      (IsSobolevHarmonicOn.linearCombination μ hQ hu (N b))
    intro φ hφ
    change energyForm μ hQ (v - (c • η + sobolevColumnMap μ hQ u (N b))) φ = 0
    rw [energyForm_sub_left, hv φ hφ, haff φ hφ, sub_self]
  refine ⟨c, b, w, rfl, hwharm, ?_, hb⟩
  have hηs := ae_restrict_of_ae_restrict_of_subset hsΩ hη
  change SobolevSpace.restrictLp μ hQ s w =
    SobolevSpace.restrictLp μ hQ s v - affineProjection μ hQ u s hfin (SobolevSpace.restrictLp μ hQ s v)
  rw [hfit, affineCoordinateMap_apply]
  dsimp only [w]
  rw [map_sub, map_add, map_smul, restrictLp_eq_one_of_representative μ hQ η s hfin hηs]

end RegularPointCoordinates

end

end OAI
