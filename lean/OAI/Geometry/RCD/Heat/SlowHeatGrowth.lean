import OAI.Geometry.RCD.Heat.RelativeHeatMean
import OAI.Geometry.RCD.Coordinates.WeightedInverse

namespace OAI

/-! # Slow growth of the actual heat frames from relative mean comparison -/

open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

/-- Fixed tolerances small enough for the square-inverse growth in the
cumulative heat argument. The comparison is in the original frame. -/
theorem slow_heat_step_of_relative_means {r s q t : ℝ}
    (hr : 0 ≤ r) (hmean : (1 - (1 / 64 : ℝ)) * r ≤ s)
    (hq : q ≤ (1 + (1 / 64 : ℝ)) * r)
    (ht : (1 - (1 / 64 : ℝ)) * s ≤ t) :
    q ≤ (9 / 8 : ℝ) * t := by
  nlinarith

/-- Iterating adjacent quadratic comparisons costs an arbitrarily fixed
small geometric factor, here 9/8 rather than the coarse factor two. -/
theorem geometric_form_growth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : ℕ → E →L[ℝ] E) {g : ℝ} (hg : 0 ≤ g)
    (hstep : ∀ i v, ⟪v, Q i v⟫_ℝ ≤ g * ⟪v, Q (i + 1) v⟫_ℝ)
    {j i : ℕ} (hji : j ≤ i) (v : E) :
    ⟪v, Q j v⟫_ℝ ≤ g ^ (i - j) * ⟪v, Q i v⟫_ℝ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
  simp only [Nat.add_sub_cancel_left]
  clear hji
  induction d with
  | zero => simp
  | succ d ih =>
      have hm := mul_le_mul_of_nonneg_left (hstep (j + d) v) (pow_nonneg hg d)
      calc
        _ ≤ g ^ d * ⟪v, Q (j + d) v⟫_ℝ := ih
        _ ≤ g ^ d * (g * ⟪v, Q (j + d + 1) v⟫_ℝ) := hm
        _ = _ := by rw [pow_succ]; ring_nf

/-- A near-identity initial heat Gram and slow growth control every inverse
vector. This is the norm hypothesis required by the cumulative comparison. -/
theorem inverse_norm_sq_of_slow_growth {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : ℕ → E ≃L[ℝ] E)
    (hstep : ∀ i v, ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ)
    (hbase : ∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ⟪v, Q 0 v⟫_ℝ)
    (i : ℕ) (v : E) :
    ‖(Q i).symm v‖ ^ 2 ≤ 4 * (81 / 64 : ℝ) ^ i * ‖v‖ ^ 2 := by
  let w := (Q i).symm v
  have hg := geometric_form_growth (fun j => (Q j : E →L[ℝ] E))
    (by norm_num : (0 : ℝ) ≤ 9 / 8) hstep (Nat.zero_le i) w
  simp only [Nat.sub_zero] at hg
  have hw : Q i w = v := (Q i).apply_symm_apply v
  have hb := (hbase w).trans hg
  change (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ (9 / 8 : ℝ) ^ i * ⟪w, Q i w⟫_ℝ at hb
  rw [hw] at hb
  have hcs : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
  have hp : 0 ≤ (9 / 8 : ℝ) ^ i := pow_nonneg (by norm_num) i
  have hbound : ‖w‖ ≤ 2 * (9 / 8 : ℝ) ^ i * ‖v‖ := by
    by_cases hz : ‖w‖ = 0
    · rw [hz]; positivity
    have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hm := mul_le_mul_of_nonneg_left hcs hp
    nlinarith
  have hs := pow_le_pow_left₀ (norm_nonneg w) hbound 2
  have hpow : ((9 / 8 : ℝ) ^ i) ^ 2 = (81 / 64 : ℝ) ^ i := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  change ‖w‖ ^ 2 ≤ _
  calc
    _ ≤ (2 * (9 / 8 : ℝ) ^ i * ‖v‖) ^ 2 := hs
    _ = _ := by rw [mul_pow, mul_pow, hpow]; ring

/-- Slow growth and positivity imply the relatively small decrement used
in the inverse-energy telescope. -/
theorem half_decrement_of_slow_step {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q P : E →L[ℝ] E) (hP : P.IsPositive)
    (hstep : ∀ v, ⟪v, Q v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, P v⟫_ℝ) (v : E) :
    ⟪v, (Q - P) v⟫_ℝ ≤ (1 / 2 : ℝ) * ⟪v, Q v⟫_ℝ := by
  simp only [sub_apply, inner_sub_right]
  linarith [hstep v, hP.inner_nonneg_right v]

/-- The slow step for the same original coordinate frame follows from
its adjacent mean comparison and the two relative heat comparisons. -/
theorem conjugated_adjacent_heat_step {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (A S : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    {p : X} {r ε : ℝ} {w : X → Euclidean (m + 1)}
    (hr : 0 < r) (hscale : a * (3 * (r / 2)) ≤ 1) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 64)
    (hfirst : FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p r ε
      (transformedColumn (hausdorff (m + 1) X) hX.quadratic u A) w)
    (hA : IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (Metric.ball p r) measurableSet_ball A)
    (hS : IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (Metric.ball p (r / 2)) measurableSet_ball S)
    (Q P : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))
    (hQ : ‖(A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
      (Q.comp (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
        ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤ 1 / 64)
    (hP : ‖(S : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
      (P.comp (S : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
        ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤ 1 / 64)
    (v : Euclidean (m + 1)) :
    ⟪v, Q v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, P v⟫_ℝ := by
  let μ := hausdorff (m + 1) X
  let U := sobolevColumnMap μ hX.quadratic u
  have hb := normalized_adjacent_mean_comparison m hX ha hBG u A hr hscale hε hfirst hA v
  have hpos := (sobolevMeanGram_isPositive μ hX.quadratic U
    (Metric.ball p r) measurableSet_ball).inner_nonneg_right v
  have hb' : (1 - (1 / 64 : ℝ)) *
      ⟪v, sobolevMeanGram μ hX.quadratic U (Metric.ball p r) measurableSet_ball v⟫_ℝ ≤
      ⟪v, sobolevMeanGram μ hX.quadratic U (Metric.ball p (r / 2)) measurableSet_ball v⟫_ℝ := by
    have hm := mul_le_mul_of_nonneg_right hsmall hpos
    linarith [hb.1]
  have hbig := relative_heat_mean_of_conjugated_norm μ hX.quadratic U _ measurableSet_ball A hA Q hQ v
  have hsmall' := relative_heat_mean_of_conjugated_norm μ hX.quadratic U _ measurableSet_ball S hS P hP v
  exact slow_heat_step_of_relative_means hpos hb' hbig.2 hsmall'.1

end RegularPointCoordinates

end

end OAI
