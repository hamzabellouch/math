import OAI.Geometry.RCD.Harmonic.AffineForcingBound
import OAI.Geometry.RCD.Harmonic.ScaledHarmonicAffine

namespace OAI

/-! # Radius-weighted forcing coefficients before residual normalization -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The forcing coefficients are controlled by the small inner residual
and its radial derivative, rather than by the full size of the projection. -/
theorem weighted_projected_euler_coefficient_bound {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f w η e : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (ell : Euclidean n) (k R : ℝ) {H α Cg Cw E : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ c a, |c| + R * ‖N.symm a‖ ≤ H *
      ‖normalizeLocalL2 μ Ω hfin (affineCoordinateMap μ hQ u Ω hfin (c, a))‖)
    (heuler : localRadialDerivative μ hQ Ω f hf w = SobolevSpace.restrictLp μ hQ Ω
      (w + sobolevColumnMap μ hQ u ell + k • η + e))
    (hD : ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω f hf w)‖ ≤ Cg * α)
    (hw : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω w)‖ ≤ Cw * α)
    (he : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω e)‖ ≤ E) :
    |k| + R * ‖N.symm ell‖ ≤ H * ((Cg + Cw) * α + E) := by
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


omit μ hQ in
/-- On the half ball, the affine forcing is bounded by the original
residual norm and its Euler error. This supplies the coefficients needed
by radial transport without assuming their smallness. -/
theorem LocalHarmonicL2GradientInput.scaled_forcing_coefficients
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (f w η e : SobolevSpace (hausdorff n X) hX.quadratic) (B : ℝ), 0 ≤ B →
      ∀ hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R / 2)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ B ^ 2,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p (R / 2))] fun _ => (1 : ℝ)) →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n) (ell : Euclidean n) (k H V E : ℝ),
      0 ≤ H → 0 ≤ V → 0 ≤ E →
      (hausdorff n X).real (ball p R) ≤ V ^ 2 * (hausdorff n X).real (ball p (R / 2)) →
      (∀ c a, |c| + R * ‖N.symm a‖ ≤ H *
        ‖normalizeLocalL2 (hausdorff n X) (ball p (R / 2))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p (R / 2))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖) →
      (localRadialDerivative (hausdorff n X) hX.quadratic (ball p (R / 2)) f hf w =
        SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (R / 2))
          (w + sobolevColumnMap (hausdorff n X) hX.quadratic u ell + k • η + e)) →
      ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) e)‖ ≤ E →
      |k| + R * ‖N.symm ell‖ ≤ H *
        ((B * C / R + V) * ‖normalizeLocalL2 (hausdorff n X) (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ + V * E) := by
  obtain ⟨C, hC, hrad⟩ := hinput.radial_derivative_bound hn hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv f w η e B hB hf hw hη u N ell k H V E hH hV hE hvol hbound heuler he
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let α := ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp μ hQ (ball p R) w)‖
  have hs : ball p (R / 2) ⊆ ball p R := ball_subset_ball (by linarith)
  have hpos (r : ℝ) (hr : 0 < r) : 0 < μ.real (ball p r) :=
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport p r hr))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hrestrict (q : SobolevSpace μ hQ) (A : ℝ) (hA : 0 ≤ A)
      (hq : ‖normalizeLocalL2 μ (ball p R) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball p R) q)‖ ≤ A) :
      ‖normalizeLocalL2 μ (ball p (R / 2)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hQ (ball p (R / 2)) q)‖ ≤ V * A :=
    normalized_fit_restrict_norm μ hQ hs _ _ (hpos R hR) (hpos (R / 2) (by linarith))
      q hV hA hvol hq
  have hD : ‖normalizeLocalL2 μ (ball p (R / 2))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (localRadialDerivative μ hQ (ball p (R / 2)) f hf w)‖ ≤ (B * C / R) * α := by
    exact hrad p R hR hcurv f w B hB hf hw
  exact weighted_projected_euler_coefficient_bound μ hQ (ball p (R / 2)) _ f w η e hf hη u N ell k R hH
    hbound heuler hD (hrestrict w α (norm_nonneg _) le_rfl) (hrestrict e E hE he)



omit [BorelSpace X] [ProperSpace X] in
/-- The exact-frame coefficient estimate controls the forcing on the
larger transport ball, including its constant and Sobolev error. -/
theorem weighted_affine_forcing_norm_bound {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (hpos : μ Ω ≠ 0) (η e : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (ell : Euclidean n) (k : ℝ) {R L C D α s : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hD : 0 ≤ D) (hα : 0 ≤ α)
    (hU : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U ell))‖ ≤ L * (R * ‖N.symm ell‖))
    (hcoeff : |k| + R * ‖N.symm ell‖ ≤ C * (α + s))
    (he : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω e)‖ ≤ D * s) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U ell + k • η + e))‖ ≤
      ((1 + L) * C + D) * (α + s) := by
  have hconst : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (k • η))‖ = |k| := by
    rw [map_smul, restrictLp_eq_one_of_representative μ hQ η Ω hfin hη,
      normalized_constant_norm μ Ω hfin hpos]
  have hsum : L * (R * ‖N.symm ell‖) + |k| ≤ (1 + L) * (|k| + R * ‖N.symm ell‖) := by
    nlinarith [abs_nonneg k, norm_nonneg (N.symm ell), mul_nonneg hL (abs_nonneg k), mul_nonneg hR (norm_nonneg (N.symm ell))]
  have hb := hsum.trans (mul_le_mul_of_nonneg_left hcoeff (by positivity : 0 ≤ 1 + L))
  rw [map_add, map_add]
  simp only [normalizeLocalL2, smul_add] at hU he hconst ⊢
  apply le_trans ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
  rw [hconst]
  have hh := add_le_add (add_le_add hU (le_rfl : |k| ≤ |k|)) he
  exact hh.trans (by nlinarith only [hb, mul_nonneg hD hα])


end RegularPointCoordinates

end

end OAI
