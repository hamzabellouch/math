import OAI.Probability.InvariantIsing.Magnetic.RestrictedBlockSpinEvaluation
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPathConvergence

namespace OAI

/-! Uniform replacement in the actual finite constrained cavity spin
test, with arbitrary bounded common-level tests and growing depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma fieldLevel_test_path_error (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (Φ : ℝ → ℝ) (p r : OverlapPath) {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    |(∫ s, Φ (q (fieldLevelIndex h s)) * p s ∂pathMeasure) -
      (∫ s, Φ (q (fieldLevelIndex h s)) * r s ∂pathMeasure)| ≤
      C * ∫ s, |p s - r s| ∂pathMeasure := by
  have hC : 0 ≤ C := (abs_nonneg (Φ 0)).trans (hΦ 0)
  have hm : Measurable (fun s => Φ (q (fieldLevelIndex h s))) :=
    (measurable_of_finite (fun i => Φ (q i))).comp (fieldLevelIndex_monotone h).measurable
  have hi (v : OverlapPath) : Integrable (fun s => Φ (q (fieldLevelIndex h s)) * v s) pathMeasure := by
    apply integrable_of_measurable_abs_le (hm.mul v.measurable) (c := C)
    intro s
    change |Φ (q (fieldLevelIndex h s)) * v s| ≤ C
    rw [abs_mul, abs_of_nonneg (v.nonneg s)]
    exact (mul_le_mul_of_nonneg_left (v.le_one s) (abs_nonneg _)).trans (by simpa using hΦ _)
  have hid : Integrable (fun s => Φ (q (fieldLevelIndex h s)) * (p s - r s)) pathMeasure := by
    apply ((hi p).sub (hi r)).congr
    exact Eventually.of_forall (fun s => by dsimp; ring)
  have he : (∫ s, Φ (q (fieldLevelIndex h s)) * p s ∂pathMeasure) -
      (∫ s, Φ (q (fieldLevelIndex h s)) * r s ∂pathMeasure) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * (p s - r s) ∂pathMeasure := by
    rw [← integral_sub (hi p) (hi r)]
    congr 1
    funext s
    ring
  rw [he]
  calc
    _ ≤ ∫ s, |Φ (q (fieldLevelIndex h s)) * (p s - r s)| ∂pathMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, C * |p s - r s| ∂pathMeasure := by
      apply integral_mono hid.abs ((p.integrable.sub r.integrable).abs.const_mul C)
      intro s
      change |Φ (q (fieldLevelIndex h s)) * (p s - r s)| ≤ C * |p s - r s|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hΦ _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem restricted_field_spin_replacement
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H C : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H)
    (q : ∀ n, Fin ((h n).depth + 1) → ℝ) (Φ : ℕ → ℝ → ℝ)
    (hΦ : ∀ n x, |Φ n x| ≤ C) :
    Tendsto (fun n =>
      (∫ z, restrictedFieldBlockSpinMean (spinGroupSlice (group n) (k n))
        (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n) z (q n) (Φ n)
        ∂(vectorGaussianLaw (N n) (NNReal.mk ((h n).height 0) ((h n).nonneg 0)) :
          Measure (Fin (N n) → ℝ))) -
      (∫ s, Φ n (q n (fieldLevelIndex (h n) s)) *
        magneticBlockPath (hN n) (h n) (fun j => m n (group n j)) s ∂pathMeasure))
      atTop (𝓝 0) := by
  have he := magneticBlockPath_l1_tendsto N hN hNlim group k hk m hr hm hc h hH
  apply squeeze_zero_norm (fun n => ?_) (show Tendsto
    (fun n => C * ∫ s, |restrictedBlockOverlapPath (hN n)
      (spinGroupSlice (group n) (k n)) (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n) s -
        magneticBlockPath (hN n) (h n) (fun j => m n (group n j)) s| ∂pathMeasure)
    atTop (𝓝 0) by simpa only [mul_zero] using he.const_mul C)
  rw [Real.norm_eq_abs, restricted_field_block_spin_evaluation hpub (hN n) _ _ _ _ _ (hΦ n)]
  exact fieldLevel_test_path_error (h n) (q n) (Φ n) _ _ (hΦ n)

end InvariantIsing

end

end OAI
