import OAI.Geometry.RCD.Harmonic.CanonicalDyadicCenters

namespace OAI

/-! # One affine-center constant before all source centers and scales -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A fixed upper bound on the splitting error makes the affine-center
constant uniform in the root radius, center, sources, frames and map. -/
theorem canonical_dyadic_affine_centers_uniform {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hmean : LocalHarmonicL2MeanValueInput hX) {κ₀ deltaCap : ℝ}
    (hκ₀ : 0 ≤ κ₀) (_hcap : 0 ≤ deltaCap) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {a κ r0 B J C L δ ε : ℝ} {p : X},
    0 ≤ a → 0 ≤ δ → δ ≤ deltaCap → ∀
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
    (_hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2),
    ∀ b : Euclidean (m + 2),
      ∃ c : ℕ → ℝ, ∃ A : ℕ → Euclidean (m + 2),
      (∀ i, affineProjection (hausdorff (m + 2) X) hX.quadratic u
          (ball p (distanceSourceRadius r0 i / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (dyadicRadialTarget hX T u hbase i b) =
        affineCoordinateMap (hausdorff (m + 2) X) hX.quadratic u
          (ball p (distanceSourceRadius r0 i / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c i, A i)) ∧
      (∀ i, |c i + ⟪v p, A i⟫_ℝ| ≤ M * (distanceSourceRadius r0 i / 64) * ‖(F i).symm b‖) ∧
      Tendsto (fun i => c i + ⟪v p, A i⟫_ℝ) atTop (𝓝 0) ∧
      (∀ i, |(c i + ⟪v p, A i⟫_ℝ) - (c (i + 1) + ⟪v p, A (i + 1)⟫_ℝ)| ≤
        M * (Real.sqrt ((hausdorff (m + 2) X).real (ball p (distanceSourceRadius r0 i / 64))) /
          Real.sqrt ((hausdorff (m + 2) X).real (ball p (distanceSourceRadius r0 (i + 1) / 64)))) *
          ((distanceSourceRadius r0 i / 64) * dyadicRadialFit hX T u L hbase i b) +
        M * ((distanceSourceRadius r0 (i + 1) / 64) * dyadicRadialFit hX T u L hbase (i + 1) b)) := by
  classical
  obtain ⟨M₀, hM₀, heval⟩ := canonical_radial_affine_center_bound hX hmean (by omega) hκ₀
  obtain ⟨M₁, hM₁, hdiff⟩ := canonical_affine_center_difference hX hmean (by omega) hκ₀
  let M := max (M₀ * ((m + 2 : ℕ) : ℝ) * (1 + deltaCap)) M₁
  have hM : 1 ≤ M := hM₁.trans (le_max_right _ _)
  refine ⟨M, hM, ?_⟩
  intro a κ r0 B J C L δ ε p ha hδ hδcap hBG S T u v hu hbase hscale hsmall F w hexact hfirst hcurv
  have hM0 : M₀ * ((m + 2 : ℕ) : ℝ) * (1 + δ) ≤ M := by
    exact (mul_le_mul_of_nonneg_left (by linarith : 1 + δ ≤ 1 + deltaCap)
      (by positivity : 0 ≤ M₀ * ((m + 2 : ℕ) : ℝ))).trans (le_max_left _ _)
  have hM1 : M₁ ≤ M := le_max_right _ _
  let μ := hausdorff (m + 2) X
  let r : ℕ → ℝ := fun i => distanceSourceRadius r0 i / 64
  have hr (i : ℕ) : 0 < r i := div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)
  have hsub (i : ℕ) : ball p (r i) ⊆ ball p r0 := by
    apply ball_subset_ball
    have hh := distanceSourceRadius_outer_le S.radius_pos.le i
    dsimp only [r]
    linarith [distanceSourceRadius_pos S.radius_pos i]
  have hv (i : ℕ) := hu.continuous.mono (hsub i)
  have hur (i : ℕ) (j : Fin (m + 2)) := (hu.harmonic j).mono μ hX.quadratic (hsub i)
  have hrep (i : ℕ) (j : Fin (m + 2)) :=
    ae_restrict_of_ae_restrict_of_subset (hsub i) (hu.representative j)
  intro b
  have hchoose (i : ℕ) : ∃ c : ℝ, ∃ A : Euclidean (m + 2),
      affineProjection μ hX.quadratic u (ball p (r i))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (dyadicRadialTarget hX T u hbase i b) =
        affineCoordinateMap μ hX.quadratic u (ball p (r i))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, A) ∧
      |c + ⟪v p, A⟫_ℝ| ≤ M * r i * ‖(F i).symm b‖ := by
    have hri : r i ≤ 4 * distanceSourceRadius r0 i := by dsimp only [r] at hr ⊢; linarith [hr i]
    have hgrad (j : Fin (m + 2)) := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show r i ≤ 2 * distanceSourceRadius r0 i by
        dsimp only [r] at hr ⊢; linarith [hr i])) ((hfirst i).gradient j)
    obtain ⟨c, A, hf, hb⟩ := heval S T i (r i) (hr i) hri (hcurv i) hδ
      u v (hur i) (hv i) (hrep i) (F i) hgrad b
      (gamma_column_le_of_diagonal_bounds μ hX.quadratic u _ L (hbase i) b)
    refine ⟨c, A, hf, hb.trans ?_⟩
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hM0 (hr i).le) (norm_nonneg ((F i).symm b))
    convert hh using 1
    ring
  choose c A hfit hsize using hchoose
  have hrad (i : ℕ) : 2 * distanceSourceRadius r0 i = r0 / (2 : ℝ) ^ i := by
    unfold distanceSourceRadius
    rw [pow_succ]
    ring
  have hgrowth := dyadic_covector_norm_reverse_growth (m + 1) hX ha hBG u p S.radius_pos hscale hδ hsmall F
    (fun i => by simpa only [hrad] using hexact i)
    (fun i => ⟨w i, by simpa only [hrad] using hfirst i⟩)
  refine ⟨c, A, hfit, hsize, ?_, ?_⟩
  · apply dyadic_affine_center_tendsto_zero S.radius_pos.le (zero_le_one.trans hM) F b
      (fun i => by simpa only [zero_add] using hgrowth 0 i b) _ hsize
  · intro i
    have hh := hdiff S T u hbase v i (i + 1) (by omega) (hcurv (i + 1))
      (hur (i + 1)) (hv (i + 1)) (hrep (i + 1)) b (A i) (A (i + 1)) (c i) (c (i + 1))
      (hfit i) (hfit (i + 1))
    apply hh.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hM1 (by positivity))
        (mul_nonneg (hr i).le (dyadicRadialFit_nonneg hX T u L hbase i b)))
      (mul_le_mul_of_nonneg_right hM1
        (mul_nonneg (hr (i + 1)).le (dyadicRadialFit_nonneg hX T u L hbase (i + 1) b)))

end RegularPointCoordinates

end

end OAI
