import OAI.Geometry.RCD.Sobolev.EulerForcing
import OAI.Geometry.RCD.Harmonic.RadialLinearRepresentatives
import OAI.Geometry.RCD.Harmonic.AffineCenterBounds

namespace OAI

/-! # The Euler equation of the actual affine projection residual -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The scalar equation obtained from Poincare is an equality in the
same local L2 space as the radial derivative. -/
theorem localRadialDerivative_eq_of_euler (Ω : Set X)
    (f v η e : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) (k : ℝ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (he : localGamma μ hQ f v =ᵐ[μ.restrict Ω]
      fun x => SobolevSpace.toLp μ hQ v x + k + SobolevSpace.toLp μ hQ e x) :
    localRadialDerivative μ hQ Ω f hf v =
      SobolevSpace.restrictLp μ hQ Ω (v + k • η + e) := by
  apply Lp.ext
  have hr := SobolevSpace.restrictLp_coe μ hQ Ω (v + k • η + e)
  filter_upwards [localRadialDerivative_representative μ hQ Ω f v hf, he, hη, hr,
    ae_restrict_of_ae (Lp.coeFn_add
      (SobolevSpace.toLp μ hQ v + k • SobolevSpace.toLp μ hQ η)
      (SobolevSpace.toLp μ hQ e)),
    ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp μ hQ v)
      (k • SobolevSpace.toLp μ hQ η)),
    ae_restrict_of_ae (Lp.coeFn_smul k (SobolevSpace.toLp μ hQ η))]
      with x hd he hη hr ha hb hc
  rw [hd, he, hr, map_add, map_add, map_smul, ha]
  simp only [Pi.add_apply, hb, hc, Pi.smul_apply, smul_eq_mul, hη, mul_one]

/-- Subtracting the actual affine fit creates precisely the coefficient
b-A b, the constant k+c, and the difference of the two known errors. -/
theorem projected_euler_identity {n : ℕ} (Ω : Set X)
    (f v η ev : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U G : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (A : Euclidean n →L[ℝ] Euclidean n) (b : Euclidean n) (k c : ℝ)
    (hv : localRadialDerivative μ hQ Ω f hf v =
      SobolevSpace.restrictLp μ hQ Ω (v + k • η + ev))
    (hG : localRadialDerivative μ hQ Ω f hf (U b) =
      SobolevSpace.restrictLp μ hQ Ω (G b)) :
    let w := v - c • η - U b
    let e := ev - (G b - U (A b))
    localRadialDerivative μ hQ Ω f hf w =
      SobolevSpace.restrictLp μ hQ Ω (w + U (b - A b) + (k + c) • η + e) := by
  dsimp only
  have hηzero := localRadialDerivative_constant μ hQ Ω f η hf 1 hη
  have hleft : localRadialDerivative μ hQ Ω f hf (v - c • η - U b) =
      SobolevSpace.restrictLp μ hQ Ω (v + k • η + ev - G b) := by
    rw [map_sub, map_sub, map_smul, hv, hG, hηzero, smul_zero, sub_zero, map_sub]
  rw [hleft]
  congr 1
  rw [map_sub, add_smul]
  module

omit [BorelSpace X] [ProperSpace X] in
/-- The projected error remains linear in the two original errors,
before any division by the residual norm. -/
theorem projected_euler_error_bound {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (ev : SobolevSpace μ hQ) (U G : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (A : Euclidean n →L[ℝ] Euclidean n) (b : Euclidean n) {E D : ℝ}
    (hev : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω ev)‖ ≤ E)
    (hfit : ‖normalizeLocalL2 μ Ω hfin
      (SobolevSpace.restrictLp μ hQ Ω (G b - U (A b)))‖ ≤ D * ‖b‖) :
    ‖normalizeLocalL2 μ Ω hfin
      (SobolevSpace.restrictLp μ hQ Ω (ev - (G b - U (A b))))‖ ≤ E + D * ‖b‖ := by
  rw [map_sub]
  simp only [normalizeLocalL2, smul_sub] at hev hfit ⊢
  exact (norm_sub_le _ _).trans (add_le_add hev hfit)

/-- The forcing coefficients are controlled by the small inner residual
and its radial derivative, rather than by the full size of the projection. -/
theorem projected_euler_coefficient_bound {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f w η e : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (ell : Euclidean n) (k : ℝ) {H α Cg Cw E : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ c a, |c| + ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 μ Ω hfin (affineCoordinateMap μ hQ u Ω hfin (c, a))‖)
    (heuler : localRadialDerivative μ hQ Ω f hf w = SobolevSpace.restrictLp μ hQ Ω
      (w + sobolevColumnMap μ hQ u ell + k • η + e))
    (hD : ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω f hf w)‖ ≤ Cg * α)
    (hw : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω w)‖ ≤ Cw * α)
    (he : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω e)‖ ≤ E) :
    |k| + ‖N.symm ell‖ ≤ H * ((Cg + Cw) * α + E) := by
  have hid : affineCoordinateMap μ hQ u Ω hfin (k, ell) =
      localRadialDerivative μ hQ Ω f hf w - SobolevSpace.restrictLp μ hQ Ω w -
        SobolevSpace.restrictLp μ hQ Ω e := by
    rw [heuler, affineCoordinateMap_apply, map_add, map_add, map_add, map_smul,
      restrictLp_eq_one_of_representative μ hQ η Ω hfin hη]
    abel
  apply (hbound k ell).trans
  apply mul_le_mul_of_nonneg_left _ hH
  rw [hid]
  simp only [normalizeLocalL2, smul_sub] at hD hw he ⊢
  apply le_trans ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl))
  exact (add_le_add (add_le_add hD hw) he).trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
