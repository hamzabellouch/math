import OAI.Geometry.RCD.Sobolev.DyadicBochnerSmallness

namespace OAI

/-! # Full Bochner smallness relative to a supplied actual heat comparison -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The local smallness argument only uses positivity and conjugated
comparison of the heat form. Its cutoff may be centered at another point. -/
theorem dyadic_bochner_mass_small_of_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) [(hausdorff (m + 1) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (M : PositiveBilinearMeasure X (Euclidean (m + 1)))
    (S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    (Q : ℕ → Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))
    (hQpos : ∀ i, (Q i).IsPositive)
    {p : X} {R e V C : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) M |K| p (2 * R) L v)
    (hR : 0 < R) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hcurv : |K| * R ^ 2 ≤ e)
    (hscale : a * (3 * R) ≤ 1)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * e) ≤ 1 / 64)
    (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
      (ball p (R / 2 ^ i)) measurableSet_ball (S i))
    (hfirst : ∀ i, ∃ w : X → Euclidean (m + 1),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (R / 2 ^ i) e
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w)
    (hvol : ∀ i, (hausdorff (m + 1) X).real (ball p (R / 2 ^ i)) ≤ V * (R / 2 ^ i) ^ (m + 1))
    (hcut : ∀ s, 0 < s → -1 ≤ K * s ^ 2 →
      Nonempty (GoodLaplacianCutoff (hausdorff (m + 1) X) hX.quadratic p s C))
    (i : ℕ) (hi : 4 ≤ i)
    (hclose : ‖(S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
      ((Q i).comp (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
      ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤ 1 / 64)
    (v : Euclidean (m + 1)) :
    ⟪v, dyadicBochnerMass M (m + 1) p R i v⟫_ℝ ≤
      (V * (16 : ℝ) ^ (m + 1) *
        (2 * C * ((m + 1 : ℕ) : ℝ) ^ 2 + 4 * (((m + 1 : ℕ) : ℝ) ^ 2 + 1))) * e *
      ⟪v, Q i v⟫_ℝ := by
  let μ := hausdorff (m + 1) X
  let : IsFiniteMeasureOnCompacts μ := ⟨fun {_s} hs => hX.finiteOnBounded _ hs.isBounded⟩
  let s := R / (2 : ℝ) ^ i
  have hs : 0 < s := div_pos hR (by positivity)
  have hsR : s ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have heq : 16 * s = R / (2 : ℝ) ^ (i - 4) := by
    have hp : (2 : ℝ) ^ i = 2 ^ (i - 4) * 16 := by
      rw [show i = (i - 4) + 4 by omega, pow_add]
      norm_num
    dsimp only [s]
    rw [hp]
    field_simp
  have hks : -1 ≤ K * s ^ 2 := by
    have hsq := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hs.le hR.le).mpr hsR) (abs_nonneg K)
    have hklo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg s)
    linarith
  let ψ := Classical.choice (hcut s hs hks)
  have hlocal : ∀ w, LocalHarmonicEnergy μ hX.quadratic (sobolevColumnMap μ hX.quadratic u)
      M |K| p (2 * s) L w := fun w => (G w).restrict μ hX.quadratic
        (ball_subset_ball (by linarith : 2 * (2 * s) ≤ 2 * (2 * R)))
  obtain ⟨w, hw⟩ := hfirst (i - 4)
  have hheat (z : Euclidean (m + 1)) :=
    (relative_heat_mean_of_conjugated_norm μ hX.quadratic (sobolevColumnMap μ hX.quadratic u)
      (ball p s) measurableSet_ball (S i) (hexact i)
      (Q i)
      hclose z).1
  have hb := bochner_mass_small_relative_to_heat μ hX.quadratic u M hlocal (S (i - 4))
    (by simpa only [heq] using hw) (by simpa only [heq] using hexact (i - 4))
    hs hsR he he1 hC (abs_nonneg K) hcurv hV
    (ENNReal.toReal_pos (ne_of_gt (hX.fullSupport p _ (by positivity)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)))
    (by simpa only [heq] using hvol (i - 4)) ψ
    (Q i)
    (hQpos i)
    (fun z => by
      simpa only [heq, dyadicMeanGram] using
        dyadic_mean_four_le_two m hX ha hBG u S hR he hscale hsmall hexact hfirst i hi z)
    (fun z => by
      have hp := (hQpos i).inner_nonneg_right z
      nlinarith [hheat z]) v
  simpa only [s, μ, ContinuousLinearEquiv.coe_coe,
    dyadicBochnerMass_inner, M.measure_real v _ measurableSet_ball] using hb

end RegularPointCoordinates

end

end OAI
