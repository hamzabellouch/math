import OAI.Geometry.RCD.Coordinates.AdjacentMeanComparison
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace OAI

/-!
# Dyadic growth and relative error of actual mean Grams

Adjacent relative estimates give an explicit outward growth bound and an
error that is linear in the original splitting error. This is the bound
needed when summing Gaussian annuli in a frame normalized at a small radius.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

/-- Adjacent relative bounds propagate outwards, retaining a factor of
the small error in the difference from the initial value. -/
theorem relative_sequence_growth {s : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (k : ℕ)
    (hs : ∀ j ≤ k, 0 ≤ s j)
    (hstep : ∀ j < k, (1 - δ) * s (j + 1) ≤ s j ∧ s j ≤ (1 + δ) * s (j + 1)) :
    s k ≤ 2 ^ k * s 0 ∧ |s k - s 0| ≤ 2 * δ * (2 ^ k - 1) * s 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := ih (fun j hj => hs j (hj.trans (Nat.le_succ k)))
        (fun j hj => hstep j (hj.trans_le (Nat.le_succ k)))
      have hnext : s (k + 1) ≤ 2 * s k := by
        have he := (hstep k (Nat.lt_succ_self k)).1
        have hp := mul_le_mul_of_nonneg_right hδhalf (hs (k + 1) le_rfl)
        linarith
      have hdiff : |s (k + 1) - s k| ≤ δ * s (k + 1) := by
        apply abs_le.mpr
        constructor
        · nlinarith [(hstep k (Nat.lt_succ_self k)).2]
        · nlinarith [(hstep k (Nat.lt_succ_self k)).1]
      have hupper : s (k + 1) ≤ 2 ^ (k + 1) * s 0 := by
        rw [pow_succ]
        nlinarith [hk.1]
      refine ⟨hupper, ?_⟩
      have ht : |s (k + 1) - s 0| ≤ |s (k + 1) - s k| + |s k - s 0| := by
        have he : s (k + 1) - s 0 = (s (k + 1) - s k) + (s k - s 0) := by ring
        rw [he]
        exact abs_add_le _ _
      have hh := mul_le_mul_of_nonneg_left hupper hδ
      rw [pow_succ] at hh ⊢
      nlinarith [hk.2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric operator norm is controlled by all of its quadratic
forms, with no extra dimension factor. -/
theorem symmetric_norm_le_of_quadratic (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ v, |⟪v, A v⟫_ℝ| ≤ C * ‖v‖ ^ 2) :
    ‖A‖ ≤ C := by
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simpa only [hv, A.rayleighQuotient_apply_zero, abs_zero] using hC
  have hp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  change |⟪A v, v⟫_ℝ / ‖v‖ ^ 2| ≤ C
  rw [real_inner_comm, abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (hbound v)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A relative quadratic estimate for two actual means is an operator
estimate in any exact normalizing frame for the reference mean. -/
theorem normalized_mean_relative_norm_le (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    [CompleteSpace E] (U : E →L[ℝ] SobolevSpace μ hQ)
    (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (A : E ≃L[ℝ] E) (hA : IsExactMeanNormalization μ hQ U s hs A)
    {C : ℝ} (hC : 0 ≤ C)
    (hrelative : ∀ v, |⟪v, sobolevMeanGram μ hQ U t ht v⟫_ℝ -
      ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ| ≤
        C * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ) :
    ‖sobolevMeanGram μ hQ (U.comp (A : E →L[ℝ] E)) t ht -
      ContinuousLinearMap.id ℝ E‖ ≤ C := by
  have hsym := (sobolevMeanGram_isPositive μ hQ (U.comp (A : E →L[ℝ] E)) t ht).isSymmetric
  apply symmetric_norm_le_of_quadratic _ (hsym.sub LinearMap.IsSymmetric.id) hC
  intro v
  have hmean (b : Set X) (hb : MeasurableSet b) :
      ⟪v, sobolevMeanGram μ hQ (U.comp (A : E →L[ℝ] E)) b hb v⟫_ℝ =
        ⟪A v, sobolevMeanGram μ hQ U b hb (A v)⟫_ℝ := by
    rw [sobolevMeanGram_comp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply]
    rfl
  have hnorm : ⟪A v, sobolevMeanGram μ hQ U s hs (A v)⟫_ℝ = ‖v‖ ^ 2 := by
    rw [← hmean s hs, hA, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  simpa only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right,
    real_inner_self_eq_norm_sq, hmean, hnorm] using hrelative (A v)

/-- Outward dyadic means of the same original harmonic map have linear
relative error. Every adjacent premise comes from the proved
normalization/Bishop--Gromov comparison. -/
theorem dyadic_mean_growth {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (p : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 2)
    (k : ℕ) (hscale : ∀ j ≤ k, a * (3 * (2 ^ j * r)) ≤ 1)
    (hnormal : ∀ j ≤ k, ∃ (A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
      (w : X → Euclidean (m + 1)),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 ^ j * r) ε
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u A) w ∧
      IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
        (ball p (2 ^ j * r)) measurableSet_ball A)
    (v : Euclidean (m + 1)) :
    let R := fun j => sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
      (ball p (2 ^ j * r)) measurableSet_ball
    ⟪v, R k v⟫_ℝ ≤ 2 ^ k * ⟪v, R 0 v⟫_ℝ ∧
      |⟪v, R k v⟫_ℝ - ⟪v, R 0 v⟫_ℝ| ≤
        2 * (((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε)) *
          (2 ^ k - 1) * ⟪v, R 0 v⟫_ℝ := by
  let μ := hausdorff (m + 1) X
  let U := sobolevColumnMap μ hX.quadratic u
  let R := fun j => sobolevMeanGram μ hX.quadratic U (ball p (2 ^ j * r)) measurableSet_ball
  let δ := ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε)
  have hδ : 0 ≤ δ := mul_nonneg (sq_nonneg _) (mul_nonneg
    (zero_le_one.trans (normalizationVolumeRatio_ge_one m)) hε)
  apply relative_sequence_growth hδ hsmall k
    (fun j _ => (sobolevMeanGram_isPositive μ hX.quadratic U
      (ball p (2 ^ j * r)) measurableSet_ball).inner_nonneg_right v)
  intro j hj
  obtain ⟨A, w, hfirst, hexact⟩ := hnormal (j + 1) hj
  have hrj : 0 < (2 : ℝ) ^ (j + 1) * r := mul_pos (pow_pos (by norm_num) _) hr
  have hhalf : (2 : ℝ) ^ (j + 1) * r / 2 = 2 ^ j * r := by rw [pow_succ]; ring
  have hb := normalized_adjacent_mean_comparison m hX ha hBG u A hrj
    (by rw [hhalf]; exact hscale j (Nat.le_of_lt hj)) hε hfirst hexact v
  simpa only [hhalf] using hb

end RegularPointCoordinates

end

end OAI
