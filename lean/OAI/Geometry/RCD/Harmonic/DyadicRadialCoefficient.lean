import OAI.Geometry.RCD.Harmonic.DyadicAffineCoefficient
import OAI.Geometry.RCD.Coordinates.NormalizedRadialCandidate
import OAI.Geometry.RCD.Harmonic.CenteredAffineDifference
import OAI.Geometry.RCD.Harmonic.DyadicRadialTargets

namespace OAI

/-! # Near-identity coefficient estimates for the actual centered radial fits -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The error of an actual centered fit bounds its coefficient error from
the identity covector. The reference candidate is the original coordinate
function, whose quantitative error has already been proved. -/
theorem dyadic_radial_coefficient_bound {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hgradient : LocalHarmonicL2GradientInput hX)
    {a κ r0 B J C Cχ L δ κ₀ ε D : ℝ} {p : X}
    (ha : 0 ≤ a) (hCχ : 0 ≤ Cχ) (hκ₀ : 0 ≤ κ₀) (hD : 0 ≤ D)
    (hscale : a * (3 * r0) ≤ 1)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ p r0)
    (T : DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C)
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ r0 →
      |(hausdorff (m + 2) X).real (ball p t) / (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4)
    (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
    (v : ℕ → X → Euclidean (m + 2)) (hδ : 0 ≤ δ)
    (hδ1 : radialNormalizationRestrictionConstant (m + 2) * δ ≤ 1)
    (hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * δ) ≤ 1 / 64)
    (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
      (ball p (2 * distanceSourceRadius r0 i)) measurableSet_ball (F i))
    (hfirst : ∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p
      (2 * distanceSourceRadius r0 i) δ (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) (v i))
    (hmetric : ∀ i, IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v i x - v i p)))
    (χ : ∀ i, GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (V : X → Euclidean (m + 2))
    (hu : FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p r0 ε u V)
    (hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2) :
    ∃ Ca : ℝ, 1 ≤ Ca ∧ ∀ (b : Euclidean (m + 2))
      (coeff : ℕ → Euclidean (m + 2)) (E : ℕ → ℝ),
    (∀ i, 0 ≤ E i) →
    (∀ i,
      ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball p (distanceSourceRadius r0 i / 64))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (dyadicRadialTarget hX T u hbase i b -
          SobolevSpace.restrictLp (hausdorff (m + 2) X) hX.quadratic
            (ball p (distanceSourceRadius r0 i / 64))
            (centeredAffineSobolev (hausdorff (m + 2) X) hX.quadratic u (χ i).sobolev (V p) (coeff i)))‖ ≤
        D * (distanceSourceRadius r0 i / 64) * ‖(F i).symm b‖ * Real.sqrt (E i)) →
    ∀ i,
      ‖(F i).symm (coeff i - b)‖ ^ 2 ≤
        2 * Ca ^ 2 * (D ^ 2 * E i + radialFitQualitativeConstant (m + 2) Cχ * δ) *
          ‖(F i).symm b‖ ^ 2 := by
  let μ := hausdorff (m + 2) X
  let hQ := hX.quadratic
  let _ := hX.openPos K (m + 2)
  let r : ℕ → ℝ := fun i => distanceSourceRadius r0 i / 64
  have hr (i : ℕ) : 0 < r i := div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)
  have hrad (i : ℕ) : 2 * distanceSourceRadius r0 i = r0 / (2 : ℝ) ^ i := by
    unfold distanceSourceRadius
    rw [pow_succ]
    ring
  have htest (i : ℕ) : (r0 / (2 : ℝ) ^ i) / 128 = r i := by
    dsimp only [r, distanceSourceRadius]
    rw [pow_succ]
    ring
  obtain ⟨Ca, hCa, hcoef⟩ := dyadic_affine_coefficient m hX hgradient hκ₀
  have hcoef' := hcoef ha S.radius_pos hscale hBG p u F hδ hsmall
    (fun i => by simpa only [hrad] using hexact i)
    (fun i => ⟨v i, by simpa only [hrad] using hfirst i⟩)
  refine ⟨Ca, hCa, ?_⟩
  intro b coeff E hE hfit i
  have hri := hr i
  have hs := distanceSourceRadius_pos S.radius_pos i
  have hle := distanceSourceRadius_outer_le S.radius_pos.le i
  have hsub : ball p (r i) ⊆ ball p r0 := ball_subset_ball (by dsimp only [r]; linarith)
  have hsub2 : ball p (2 * distanceSourceRadius r0 i) ⊆ ball p r0 := ball_subset_ball hle
  let H := centeredAffineSobolev μ hQ u (χ i).sobolev (V p) (coeff i)
  let H₀ := centeredAffineSobolev μ hQ u (T.cutoff i).sobolev (V p) b
  have hη : SobolevSpace.toLp μ hQ (χ i).sobolev =ᵐ[μ.restrict (ball p (r i))] fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (χ i).representative, ae_restrict_mem measurableSet_ball]
      with x hx hxr
    exact hx.trans ((χ i).one x hxr)
  have hζ : SobolevSpace.toLp μ hQ (T.cutoff i).sobolev =ᵐ[μ.restrict (ball p (r i))] fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (T.cutoff i).representative, ae_restrict_mem measurableSet_ball]
      with x hx hxr
    exact hx.trans ((T.cutoff i).one x ((ball_subset_ball (by dsimp only [r]; linarith)) hxr))
  have hhu (j : Fin (m + 2)) := (hu.harmonic j).mono μ hQ hsub
  have hH := centeredAffineSobolev_harmonic μ hQ u (χ i).sobolev (V p) (coeff i) _ hhu
    (isSobolevHarmonicOn_of_local_constant μ hQ _ measurableSet_ball _ 1 hη)
  have hH₀ := centeredAffineSobolev_harmonic μ hQ u (T.cutoff i).sobolev (V p) b _ hhu
    (isSobolevHarmonicOn_of_local_constant μ hQ _ measurableSet_ball _ 1 hζ)
  have hcand := T.normalized_radial_candidate μ hQ i (euclideanUnitVolume_pos (m + 2))
    hδ hδ1 hCχ (fun t ht hts => hquarter t ht (hts.trans hle)) u (F i) V (v i)
    (hu.continuous.mono hsub2) (fun j => ae_restrict_of_ae_restrict_of_subset hsub2 (hu.representative j))
    (hfirst i) (hmetric i) (χ i) b
    (gamma_column_le_of_diagonal_bounds μ hQ u _ L (hbase i) b)
  dsimp only at hcand
  have hfit2 := (sq_le_sq₀ (norm_nonneg _)
    (show 0 ≤ D * r i * ‖(F i).symm b‖ * Real.sqrt (E i) by positivity)).mpr (hfit i)
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hE i)] at hfit2
  have hdiff := normalized_two_fit_difference μ hQ
    (ne_of_lt (hX.finiteOnBounded (ball p (r i)) isBounded_ball))
    (dyadicRadialTarget hX T u hbase i b) H H₀ hfit2 hcand
  have hci := hcoef' i
  rw [htest] at hci
  have hb := hci (hcurv i) (coeff i - b) (H - H₀) (-⟪V p, coeff i - b⟫_ℝ)
    (by simpa only [sub_eq_add_neg, neg_one_smul] using
      hH.add μ hQ (hH₀.smul μ hQ (-1)))
    (centeredAffineSobolev_difference_constant μ hQ u _ (χ i).sobolev (T.cutoff i).sobolev
      (V p) (coeff i) b hη hζ)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hdiff (sq_nonneg (Ca / r i))
  convert hh using 1
  field_simp [hri.ne']
  ring

end RegularPointCoordinates

end

end OAI
