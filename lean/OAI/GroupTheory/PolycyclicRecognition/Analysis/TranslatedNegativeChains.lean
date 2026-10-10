import OAI.GroupTheory.PolycyclicRecognition.Analysis.NegativePathWords

namespace OAI

/-! # Negative chains based at arbitrary group elements -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A fixed left translate preserves a negative linear height margin,
linear radius, and all unit-step bounds. -/
theorem left_translate_negative_chains
    (η : G →* Multiplicative ℝ) (m : ℕ → ℕ) (z : ℕ → ℕ → G)
    {R gap : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap)
    (hnegative : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (z n i)).toAdd ≤ -gap * n)
    (hball : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1)
    (g : G) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (g * z n i)).toAdd ≤ -(gap / 2) * n) ∧
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (g * z n i) ≤ B * n) ∧
      ∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (g * z n i) (g * z n (i + 1)) ≤ 1 := by
  refine ⟨R + dist 1 g, add_nonneg hR dist_nonneg, ?_, ?_, ?_⟩
  · have herr : ∀ᶠ n : ℕ in atTop, (η g).toAdd ≤ (gap / 2) * n := by
      have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
        (show 0 < gap / 2 by linarith)
      exact ht.eventually (eventually_ge_atTop _)
    filter_upwards [hnegative, herr] with n hn he
    intro i hi
    rw [map_mul, toAdd_mul]
    have hh := hn i hi
    nlinarith
  · filter_upwards [hball, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    intro i hi
    have ht := dist_triangle (1 : G) g (g * z n i)
    have hd : dist g (g * z n i) = dist 1 (z n i) := by
      simpa only [mul_one] using dist_mul_left g (1 : G) (z n i)
    rw [hd] at ht
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hh := mul_le_mul_of_nonneg_left hn1' (show 0 ≤ dist 1 g from dist_nonneg)
    have hb := hn i hi
    nlinarith
  · filter_upwards [hstep] with n hn
    intro i hi
    rw [dist_mul_left]
    exact hn i hi

/-- Apply a negative-chain contraction criterion after a fixed left
translation, retaining the actual endpoint sequences. -/
theorem translated_negative_chain_endpoint_limit
    {Q : Type*} [Group Q] [TopologicalSpace Q]
    (η : G →* Multiplicative ℝ) (observe : G → Q)
    (m : ℕ → ℕ) (z : ℕ → ℕ → G) {R gap : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap)
    (hnegative : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (z n i)).toAdd ≤ -gap * n)
    (hball : ∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1)
    (base target : ℕ → G) (hbase : ∀ n, z n 0 = base n)
    (htarget : ∀ᶠ n in atTop, z n (m n) = target n)
    (g : G)
    (criterion : ∀ (z' : ℕ → ℕ → G) (R' gap' : ℝ), 0 ≤ R' → 0 < gap' →
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, (η (z' n i)).toAdd ≤ -gap' * n) →
      (∀ᶠ n : ℕ in atTop, ∀ i ≤ m n, dist 1 (z' n i) ≤ R' * n) →
      (∀ᶠ n : ℕ in atTop, ∀ i < m n, dist (z' n i) (z' n (i + 1)) ≤ 1) →
      Tendsto (fun n => (observe (z' n 0))⁻¹ * observe (z' n (m n))) atTop (𝓝 1)) :
    Tendsto (fun n => (observe (g * base n))⁻¹ * observe (g * target n)) atTop (𝓝 1) := by
  obtain ⟨B, hB, hn, hb, hs⟩ := left_translate_negative_chains η m z hR hgap
    hnegative hball hstep g
  have ht := criterion (fun n i => g * z n i) B (gap / 2) hB
    (div_pos hgap (by norm_num)) hn hb hs
  apply ht.congr'
  filter_upwards [htarget] with n he
  exact congrArg₂ (fun x y => (observe x)⁻¹ * observe y)
    (congrArg (g * ·) (hbase n)) (congrArg (g * ·) he)

end PolycyclicRecognition

end

end OAI
