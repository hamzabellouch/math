import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairTies

namespace OAI

/-! The canonical site-average overlap path and its uniform comparison
with the original constrained-block overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def magneticBlockLevel {N : ℕ} (h : FieldStep) (m : Fin N → ℝ)
    (i : Fin (h.depth + 1)) : ℝ := (N : ℝ)⁻¹ * ∑ j, magneticFieldLevel h (m j) i

lemma magneticBlockLevel_mem_unit {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (m : Fin N → ℝ) (i : Fin (h.depth + 1)) : magneticBlockLevel h m i ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg (fun j _ => (magneticFieldLevel_mem_unit h (m j) i).1))
  · calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun j _ => (magneticFieldLevel_mem_unit h (m j) i).2))
          (inv_nonneg.mpr hn.le)
      _ = 1 := by simp [hn.ne']

lemma magneticBlockLevel_monotone {N : ℕ} (h : FieldStep) (m : Fin N → ℝ) :
    Monotone (magneticBlockLevel h m) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k _ => magneticFieldLevel_monotone h (m k) hij)) (by positivity)

def magneticBlockPath {N : ℕ} (hN : 0 < N) (h : FieldStep) (m : Fin N → ℝ) : OverlapPath :=
  fieldLevelPath h (magneticBlockLevel h m) (magneticBlockLevel_monotone h m)
    (magneticBlockLevel_mem_unit hN h m)

lemma magneticBlockPairMean_comparison {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2))
    (h : FieldStep) (i : Fin (h.depth + 1)) {t : ℝ} (ht : 0 < t) :
    |restrictedBlockPairMean hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
        h (fun _ => 0) i - magneticBlockLevel h (fun j => m (group j)) i| ≤
      2 * ((N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (m (group j))) -
        constrainedBlockValue (spinGroupSlice group k) h) / t + t / 2 := by
  have he := restrictedBlockPairMean_comparison hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h (fun j => magneticBias h (m (group j))) i ht
  rw [← magneticBlockGap_eq_biasedGap hN group k hk m hm hc h,
    restrictedBlockPairMean_group_bias hN group k hk (fun a => magneticBias h (m a)) h i] at he
  exact he

lemma magneticBlockPath_l1_comparison {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hc : ∀ a, (k a : ℝ) = spinGroupSize group a * ((1 + m a) / 2))
    (h : FieldStep) {t : ℝ} (ht : 0 < t) :
    (∫ s, |restrictedBlockOverlapPath hN (spinGroupSlice group k)
        (spinGroupSlice_nonempty group k hk) h s - magneticBlockPath hN h (fun j => m (group j)) s|
      ∂pathMeasure) ≤
      2 * ((N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (m (group j))) -
        constrainedBlockValue (spinGroupSlice group k) h) / t + t / 2 := by
  let p := restrictedBlockOverlapPath hN (spinGroupSlice group k)
    (spinGroupSlice_nonempty group k hk) h
  let q := magneticBlockPath hN h (fun j => m (group j))
  calc
    _ ≤ ∫ _s, (2 * ((N : ℝ)⁻¹ * (∑ j, constrainedFieldValue h (m (group j))) -
        constrainedBlockValue (spinGroupSlice group k) h) / t + t / 2) ∂pathMeasure := by
      apply integral_mono (p.integrable.sub q.integrable).abs (integrable_const _)
      intro s
      exact magneticBlockPairMean_comparison hN group k hk m hm hc h (fieldLevelIndex h s) ht
    _ = _ := by simp

end InvariantIsing

end

end OAI
