import OAI.Geometry.RCD.Harmonic.UniformCanonicalCenters
import OAI.Geometry.RCD.Coordinates.CanonicalCenteredFits

namespace OAI

/-! # Centered radial fits with constants independent of the center and scale -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The centered-fit constant is fixed before the root radius, center,
source, harmonic map, frame, defect sequence, and splitting error. -/
theorem canonical_centered_fits_of_squared_bound_uniform {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hmean : LocalHarmonicL2MeanValueInput hX) {κ₀ deltaCap Z : ℝ}
    (hκ₀ : 0 ≤ κ₀) (hcap : 0 ≤ deltaCap) (hZ : 0 < Z) :
    ∃ D : ℝ, 0 < D ∧ ∀ {a κ r0 B J C L δ ε : ℝ} {p : X},
    ∀ (_ha : 0 ≤ a) (_hδ : 0 ≤ δ) (_hδcap : δ ≤ deltaCap)
    (_hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ p r0)
    (T : DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C)
    (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
    (v : X → Euclidean (m + 2))
    (_hu : FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p r0 ε u v)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (_hscale : a * (3 * r0) ≤ 1)
    (_hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * δ) ≤ 1 / 64)
    (F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
    (w : ℕ → X → Euclidean (m + 2))
    (_hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
      (ball p (2 * distanceSourceRadius r0 i)) measurableSet_ball (F i))
    (_hfirst : ∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p
      (2 * distanceSourceRadius r0 i) δ (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) (w i))
    (_hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2)
    (_hquarter : ∀ t : ℝ, 0 < t → t ≤ r0 →
      |(hausdorff (m + 2) X).real (ball p t) / (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4)
    (Q : ℕ → ℝ) (_hQ : ∀ i, 0 ≤ Q i) (_hQs : Summable Q)
    (_hsquare : ∀ b : Euclidean (m + 2), b ≠ 0 → ∀ i,
      (dyadicRadialFit hX T u L hbase i b) ^ 2 ≤ Z * Q i * ‖(F i).symm b‖ ^ 2),
    ∀ b : Euclidean (m + 2), b ≠ 0 →
      ∃ c : ℕ → ℝ, ∃ A : ℕ → Euclidean (m + 2),
      (∀ i, affineProjection (hausdorff (m + 2) X) hX.quadratic u
          (ball p (distanceSourceRadius r0 i / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (dyadicRadialTarget hX T u hbase i b) =
        affineCoordinateMap (hausdorff (m + 2) X) hX.quadratic u
          (ball p (distanceSourceRadius r0 i / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c i, A i)) ∧
      (∀ i, |c i + ⟪v p, A i⟫_ℝ| ≤ D * (distanceSourceRadius r0 i / 64) *
        ‖(F i).symm b‖ * Real.sqrt (symmetricDefect (7 / 8) Q i)) ∧
      (∀ i, ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball p (distanceSourceRadius r0 i / 64))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (dyadicRadialTarget hX T u hbase i b -
          affineCoordinateMap (hausdorff (m + 2) X) hX.quadratic u
            (ball p (distanceSourceRadius r0 i / 64))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (-⟪v p, A i⟫_ℝ, A i))‖ ≤
        D * (distanceSourceRadius r0 i / 64) * ‖(F i).symm b‖ *
          Real.sqrt (symmetricDefect (7 / 8) Q i)) := by
  obtain ⟨M, hM, hallcenters⟩ :=
    canonical_dyadic_affine_centers_uniform m hX hmean hκ₀ hcap
  let Λ := Real.sqrt ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ (m + 2))⁻¹)
  have hΛ : 0 ≤ Λ := Real.sqrt_nonneg _
  let H := (1 - (9 / 16 : ℝ) / Real.sqrt (7 / 8))⁻¹ * (1 + (Real.sqrt (7 / 8))⁻¹)
  have hroot : (9 / 16 : ℝ) < Real.sqrt (7 / 8) := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 8)
    nlinarith [Real.sqrt_nonneg (7 / 8)]
  have hH : 0 ≤ H := by
    dsimp only [H]
    have hh : (9 / 16 : ℝ) / Real.sqrt (7 / 8) < 1 :=
      (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr hroot
    positivity
  let Dc := (M * (Λ + 1) * Real.sqrt Z) * H
  have hDc : 0 ≤ Dc := by dsimp only [Dc]; positivity
  let D := Real.sqrt Z + Dc
  have hD : 0 < D := add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hZ) hDc
  refine ⟨D, hD, ?_⟩
  intro a κ r0 B J C L δ ε p ha hδ hδcap hBG S T u v hu hbase hscale hsmall
    F w hexact hfirst hcurv hquarter Q hQ hQs hsquare
  let μ := hausdorff (m + 2) X
  let r : ℕ → ℝ := fun i => distanceSourceRadius r0 i / 64
  have hr (i : ℕ) : 0 < r i := div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)
  have hradius (i k : ℕ) : r (i + k) = (1 / 2 : ℝ) ^ k * r i := by
    exact distanceSourceRadius_testing_shift r0 i k
  have hrle (i : ℕ) : r i ≤ r0 := by
    have hh := distanceSourceRadius_outer_le S.radius_pos.le i
    have hs := distanceSourceRadius_pos S.radius_pos i
    dsimp only [r]
    linarith
  have hratio (i : ℕ) : Real.sqrt (μ.real (ball p (r i))) /
      Real.sqrt (μ.real (ball p (r (i + 1)))) ≤ Λ := by
    rw [hradius i 1, pow_one]
    exact radial_sqrt_volume_ratio (hr i) (by norm_num) (euclideanUnitVolume_pos (m + 2))
      (measureReal_nonneg) (hquarter _ (hr i) (hrle i))
      (by simpa only [hradius i 1, pow_one] using hquarter _ (hr (i + 1)) (hrle (i + 1)))
  have hrad (i : ℕ) : 2 * distanceSourceRadius r0 i = r0 / (2 : ℝ) ^ i := by
    unfold distanceSourceRadius
    rw [pow_succ]
    ring
  have hgrowth := dyadic_covector_norm_reverse_growth (m + 1) hX ha hBG u p S.radius_pos hscale hδ hsmall F
    (fun i => by simpa only [hrad] using hexact i)
    (fun i => ⟨w i, by simpa only [hrad] using hfirst i⟩)
  have hcenters := hallcenters ha hδ hδcap hBG S T u v hu hbase hscale hsmall
    F w hexact hfirst hcurv
  intro b hb
  obtain ⟨c, A, hfit, _hsize, hlim, hdiff⟩ := hcenters b
  have hc (i : ℕ) : |c i + ⟪v p, A i⟫_ℝ| ≤
      Dc * r i * ‖(F i).symm b‖ * Real.sqrt (symmetricDefect (7 / 8) Q i) := by
    have hh := weighted_centers_from_squared_fit (by norm_num : (0 : ℝ) < 7 / 8)
      (by norm_num : (7 / 8 : ℝ) < 1) hroot (zero_le_one.trans hM) hΛ hZ.le hQ hQs
      (fun j => (hr j).le) (fun j => norm_nonneg ((F j).symm b))
      (fun j => dyadicRadialFit_nonneg hX T u L hbase j b) hradius
      (fun j k => hgrowth j k b) hlim (hsquare b hb) (fun j => ?_) i
    · convert hh using 1
      dsimp only [Dc, H]
      ring
    · have hs := hdiff j
      have hv := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hratio j) (zero_le_one.trans hM))
        (mul_nonneg (hr j).le (dyadicRadialFit_nonneg hX T u L hbase j b))
      apply hs.trans
      exact add_le_add (hv.trans_eq (by ring)) (le_of_eq (by dsimp only [r]; ring))
  have herror (i : ℕ) : dyadicRadialFit hX T u L hbase i b ≤
      Real.sqrt Z * ‖(F i).symm b‖ * Real.sqrt (symmetricDefect (7 / 8) Q i) := by
    have hsq := hsquare b hb i
    have hbound : dyadicRadialFit hX T u L hbase i b ≤ Real.sqrt Z * ‖(F i).symm b‖ * Real.sqrt (Q i) := by
      apply (sq_le_sq₀ (dyadicRadialFit_nonneg hX T u L hbase i b) (by positivity)).mp
      calc
        _ ≤ Z * Q i * ‖(F i).symm b‖ ^ 2 := hsq
        _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hZ.le, Real.sq_sqrt (hQ i)]; ring
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (le_symmetricDefect (by norm_num) (by norm_num) hQ hQs i)) (by positivity))
  refine ⟨c, A, hfit, ?_, ?_⟩
  · intro i
    exact (hc i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show Dc ≤ D by exact le_add_of_nonneg_left (Real.sqrt_nonneg Z)) (hr i).le) (norm_nonneg _))
      (Real.sqrt_nonneg _))
  · intro i
    have hs := centered_affineFit_error μ hX.quadratic u (ball p (r i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (ne_of_gt (hX.fullSupport p _ (hr i)))
      (v p) (dyadicRadialTarget hX T u hbase i b) (c i) (A i) (hfit i)
    rw [dyadicRadialTarget_residual_norm hX T u hbase i b] at hs
    have hh := add_le_add (mul_le_mul_of_nonneg_left (herror i) (hr i).le) (hc i)
    exact hs.trans (hh.trans_eq (by dsimp only [D]; ring))

end RegularPointCoordinates

end

end OAI
