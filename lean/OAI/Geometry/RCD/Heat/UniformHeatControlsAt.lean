import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.UniformHeatCumulative
import OAI.Geometry.RCD.Heat.HeatControls
import OAI.Geometry.RCD.Heat.DyadicHeatAtStability
import OAI.Geometry.RCD.Heat.UniformHeatAtBounds
import OAI.Geometry.RCD.Metric.DyadicMassComparison

namespace OAI

/-! # Uniform actual heat controls before choosing the map or heat pole -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- One tolerance, decrement constant and comparison index work for all
maps and poles satisfying the displayed geometric bounds. The cutoff may
be fixed independently of the evaluation pole. -/
theorem uniform_heat_controls_at_of_splitting {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    {L B Vlo Vhi C η lambda : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hVlo : 0 < Vlo) (hVhi : 0 < Vhi) (hC : 0 ≤ C) (hη : 0 ≤ η) (hlambda : 0 < lambda) :
    ∃ ε εmass C₁ : ℝ, ∃ N : ℕ,
      0 < ε ∧ ε ≤ 1 ∧ 0 ≤ εmass ∧ 0 ≤ C₁ ∧
      2 * C₁ * (2 * geometricIntervalConstant ((3 / 4 : ℝ) * (9 / 8))) * εmass ≤ 1 / 2 ∧
      ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 → a * (3 * R) ≤ 1 →
      ∀ (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
        (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
        (S : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
        (p : X) (e : ℝ) (L₀ : ℝ≥0)
        (_G : ∀ v, LocalHarmonicEnergy (hausdorff (m + 2) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) M |K| p (2 * R) L₀ v),
      0 ≤ e → e ≤ ε → |K| * R ^ 2 ≤ e → 2 * |K| * (L₀ : ℝ) ^ 2 + η ≤ lambda →
      ‖(S 0 : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))‖ ^ 2 ≤ B →
      (∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
        (ball p (R / 2 ^ i)) measurableSet_ball (S i)) →
      (∀ i, ∃ w : X → Euclidean (m + 2),
        FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p (R / 2 ^ i) e
          (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (S i)) w) →
      (∀ s, 0 < s → -1 ≤ K * s ^ 2 →
        Nonempty (GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p s C)) →
      (∀ i y, dist p y ≤ 2 * R →
        ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          Vlo * (R / 2 ^ i) ^ (m + 2) ≤ (hausdorff (m + 2) X).real (ball y (Real.sqrt t)) ∧
          (hausdorff (m + 2) X).real (ball y (Real.sqrt t)) ≤ Vhi * (R / 2 ^ i) ^ (m + 2)) →
      (∀ v : Euclidean (m + 2), ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p R),
        localGamma (hausdorff (m + 2) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u v)
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u v) x ≤ L * ‖v‖ ^ 2) →
      ∀ (q : X) (r ρ Ccut : ℝ)
        (Gheat : ∀ v, LocalHarmonicEnergy (hausdorff (m + 2) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) M |K| q r L₀ v)
        (χ : GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic q ρ Ccut),
      0 < ρ → ρ < r →
      (∀ x ∈ ball p (R / 4), (χ.weight : X → ℝ) x = 1) →
      (∀ x ∉ ball p R, (χ.weight : X → ℝ) x = 0) →
      ∀ J₀ : ℕ,
      (∀ i, J₀ ≤ i → ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
        ‖harmonicHeatError (hausdorff (m + 2) X) hX.quadratic (k := ker) Gheat χ t p‖ ≤ η) →
      ∀ J : ℕ, max 4 (max N J₀) ≤ J →
      EventualHeatControls
        (dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ p hR hlambda)
        (dyadicBochnerMass M (m + 2) p R)
        (dyadicBochnerEnvelope M (m + 2) p R) J εmass C₁ ∧
      ∀ i, J ≤ i → ∀ v,
        (1 - 1 / 64 : ℝ) * ⟪v, sobolevMeanGram (hausdorff (m + 2) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
          (ball p (R / 2 ^ i)) measurableSet_ball v⟫_ℝ ≤
            ⟪v, dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
              (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ p hR hlambda i v⟫_ℝ ∧
        ⟪v, dyadicHeatGramAt (hausdorff (m + 2) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u) χ p hR hlambda i v⟫_ℝ ≤
            (1 + 1 / 64 : ℝ) * ⟪v, sobolevMeanGram (hausdorff (m + 2) X) hX.quadratic
              (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
              (ball p (R / 2 ^ i)) measurableSet_ball v⟫_ℝ := by
  let μ := hausdorff (m + 2) X
  obtain ⟨C₁, hC₁, hdecrement⟩ := exists_uniform_supported_heat_bound_at μ hX.quadratic hk m hg
    hVlo hVhi hη hlambda
  obtain ⟨N, e₀, he₀, hcompare⟩ := dyadic_heat_mean_comparison (m + 1) hX ha hBG hk hg
    hL hB hVhi.le hVlo lambda (by norm_num : (0 : ℝ) < 1 / 64)
  let M₀ := Vhi * (16 : ℝ) ^ (m + 2) *
    (2 * C * ((m + 2 : ℕ) : ℝ) ^ 2 + 4 * (((m + 2 : ℕ) : ℝ) ^ 2 + 1))
  let W := 2 * geometricIntervalConstant ((3 / 4 : ℝ) * (9 / 8))
  have hM₀ : 0 ≤ M₀ := by dsimp only [M₀]; positivity
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (geometricIntervalConstant_nonneg (by norm_num))
  obtain ⟨ε, hε, hεcap, hε1, htolerance⟩ := exists_cumulative_error_tolerance
    (mul_nonneg (sq_nonneg (((m + 2 : ℕ) : ℝ)))
      (zero_le_one.trans (normalizationVolumeRatio_ge_one (m + 1)))) hC₁.le hW hM₀ he₀
  refine ⟨ε, M₀ * ε, C₁, N, hε, hε1, mul_nonneg hM₀ hε.le, hC₁.le,
    (htolerance ε hε.le le_rfl).2, ?_⟩
  intro R hR hR1 hscale u M S p e L₀ G he heε hcurv hreg hS0 hexact hfirst
    hcut hvolume hgradient q r ρ Ccut Gheat χ hρ hρR hχone hχzero J₀ herror J hJ
  have htol := htolerance e he heε
  have hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * e) ≤ 1 / 64 := by
    simpa only [mul_assoc] using htol.1
  have he1 := heε.trans hε1
  have hvol i y (hy : dist p y ≤ 2 * R) :
      Vlo * (R / 2 ^ i) ^ (m + 2) ≤ μ.real (ball y (R / 2 ^ i)) ∧
      μ.real (ball y (R / 2 ^ i)) ≤ Vhi * (R / 2 ^ i) ^ (m + 2) := by
    have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have h := hvolume i y hy ((R / 2 ^ i) ^ 2) ⟨by nlinarith [sq_pos_of_pos hs], le_rfl⟩
    simpa only [Real.sqrt_sq hs.le] using h
  have hvolp i : μ.real (ball p (R / 2 ^ i)) ≤ Vhi * (R / 2 ^ i) ^ (m + 2) :=
    (hvol i p (by simp only [dist_self]; positivity)).2
  have hsupport y (hy : (χ.weight : X → ℝ) y ≠ 0) : dist p y ≤ 2 * R := by
    have hb : y ∈ ball p R := by
      by_contra hn
      exact hy (hχzero y hn)
    have hd : dist p y < R := by simpa only [mem_ball, dist_comm] using hb
    linarith
  have hclose i (hi : J ≤ i) :
      ‖(S i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint.comp
        ((dyadicHeatGramAt μ hX.quadratic hk (sobolevColumnMap μ hX.quadratic u) χ p hR hlambda i :
          Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).comp
          (S i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))) -
        ContinuousLinearMap.id ℝ (Euclidean (m + 2))‖ ≤ 1 / 64 := by
    have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hc := hcompare R hR hR1 hscale u p S e he (heε.trans hεcap)
      (by nlinarith [htol.1]) hS0 hexact hfirst χ.weight χ.weight.continuous
      (χ.hasCompactSupport μ hX.quadratic) χ.bounds hχzero hχone hvolp hgradient
      (fun j y hy => (hvol j y (hsupport y hy)).1) i (by omega) hs
    exact hc.le
  let Q := dyadicHeatGramAt μ hX.quadratic hk (sobolevColumnMap μ hX.quadratic u) χ p hR hlambda
  have hpos i : (Q i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).IsPositive :=
    dyadicHeatGramAt_isPositive μ hX.quadratic hk _ χ p hR hlambda i
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact dyadic_heat_at_step_of_conjugated_comparison (m + 1) hX ha hBG hk u S χ
      hR hlambda he hscale hsmall hexact hfirst J hclose
  · intro i hi v
    apply hdecrement R hR hR1 q r |K| L₀ _ M Gheat ρ Ccut χ p
      hρ hρR (abs_nonneg K) hreg hχone hχzero
    · intro j t ht y hy
      have hs : R / (2 : ℝ) ^ j ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
      have hd : dist p y ≤ 2 * R := by
        have hd : dist p y < R / (2 : ℝ) ^ j := by simpa only [mem_ball, dist_comm] using hy
        linarith
      have hv := hvolume j y hd t ht
      exact ⟨(mul_pos hVlo (pow_pos (div_pos hR (by positivity)) _)).trans_le hv.1, hv.2⟩
    · intro j t ht y hy
      exact (hvolume j y (hsupport y hy) t ht).1
    · omega
    · exact herror i (by omega)
  · intro i hi v
    have hm := dyadic_bochner_mass_small_of_comparison (m + 1) hX ha hBG u M S
      (fun j => (Q j : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))) hpos G hR he he1
      hVhi.le hC hcurv hscale hsmall hexact hfirst hvolp hcut i
      (by omega) (hclose i hi) v
    exact hm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heε hM₀)
      ((hpos i).inner_nonneg_right v))

  · intro i hi v
    exact relative_heat_mean_of_conjugated_norm μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic u) (ball p (R / 2 ^ i)) measurableSet_ball
      (S i) (hexact i) (Q i) (hclose i hi) v

end RegularPointCoordinates

end

end OAI
