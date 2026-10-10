import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

namespace Pureness
open Filter Topology
open scoped NNReal ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] lemma normalizedRootRank_zero (τ : TracialState A) : normalizedRootRank τ 0 = 0 := by
  simp only [normalizedRootRank, normalizedRoot, normalizePositive_zero, CFC.nnrpow_eq_pow,
    CFC.zero_nnrpow, map_zero, Complex.zero_re, ENNReal.ofReal_zero, iSup_const]

lemma normalizedRoot_tendsto {a : ℕ → A} {c : A} (ha : ∀ n, 0 ≤ a n)
    (hc : 0 ≤ c) (hc0 : c ≠ 0) (ht : Tendsto a atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n => normalizedRoot (a n) j) atTop (𝓝 (normalizedRoot c j)) := by
  have hn : Tendsto (fun n => normalizePositive (a n)) atTop (𝓝 (normalizePositive c)) :=
    (ht.norm.inv₀ (norm_ne_zero_iff.mpr hc0)).smul ht
  have hw : Tendsto (fun n => normalizePositive (a n)) atTop
      (𝓝[{a : A | 0 ≤ a}] (normalizePositive c)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hn, Eventually.of_forall (fun n => normalizePositive_nonneg _ (ha n))⟩
  have hcont : Tendsto (fun a : A => CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹))
      (𝓝[{a : A | 0 ≤ a}] (normalizePositive c)) (𝓝 (normalizedRoot c j)) :=
    (CFC.continuousOn_nnrpow (((j : ℝ≥0) + 1)⁻¹)).continuousWithinAt
      (normalizePositive_nonneg c hc)
  exact hcont.comp hw

lemma rank_le_of_tendsto (τ : TracialState A) {a : ℕ → A} {c : A} {r : ℝ≥0∞}
    (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : Tendsto a atTop (𝓝 c))
    (hr : ∀ n, normalizedRootRank τ (a n) ≤ r) : normalizedRootRank τ c ≤ r := by
  by_cases hc0 : c = 0
  · simp only [hc0, normalizedRootRank_zero, zero_le]
  apply iSup_le
  intro j
  have htj : Tendsto (fun n => ENNReal.ofReal (τ.functional (normalizedRoot (a n) j)).re)
      atTop (𝓝 (ENNReal.ofReal (τ.functional (normalizedRoot c j)).re)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp
        ((map_continuous τ.functional).continuousAt.tendsto.comp
          (normalizedRoot_tendsto ha hc hc0 ht j)))
  apply le_of_tendsto htj
  exact Eventually.of_forall fun n =>
    (le_iSup (fun j => ENNReal.ofReal (τ.functional (normalizedRoot (a n) j)).re) j).trans (hr n)

lemma rank_conjugate_le (τ : TracialState A) (b v : A) (hb : 0 ≤ b) :
    normalizedRootRank τ (star v * b * v) ≤ normalizedRootRank τ b := by
  let x := CFC.sqrt b * v
  have heq : star x * x = star v * b * v := by
    dsimp [x]
    simp only [star_mul, (CFC.sqrt_nonneg b).star_eq]
    calc
      _ = star v * (CFC.sqrt b * CFC.sqrt b) * v := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self b hb]
  rw [← heq, rank_star_mul_self τ x]
  apply hereditary_rank_domination τ b (x * star x) hb (mul_star_self_nonneg x)
  have he : x * star x = CFC.sqrt b * (v * star v) * CFC.sqrt b := by
    simp only [x, star_mul, (CFC.sqrt_nonneg b).star_eq, mul_assoc]
  rw [he]
  exact sqrt_sandwich_mem_hereditary b _ hb

theorem CuntzSubequiv.rank_le {a b : A} (hab : CuntzSubequiv a b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (τ : TracialState A) :
    normalizedRootRank τ a ≤ normalizedRootRank τ b := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence a b).mp hab
  exact rank_le_of_tendsto τ (fun n => star_left_conjugate_nonneg hb (v n)) ha hv
    (fun n => rank_conjugate_le τ b (v n) hb)

end Pureness
end

end OAI
