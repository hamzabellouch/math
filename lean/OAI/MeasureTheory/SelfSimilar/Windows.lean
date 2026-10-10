import OAI.MeasureTheory.SelfSimilar.SumsetBound

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Windows

theorem ceiling_increment (x y : ℝ) :
    (⌈y⌉ : ℝ) - (⌈x⌉ : ℝ) ≤ y - x + 1 := by
  linarith [Int.le_ceil x, Int.ceil_lt_add_one y]

theorem finer_window_before {σ : ℕ → ℝ} (hσ : Monotone σ)
    {j k n : ℕ} {L a B : ℤ} {d : ℝ}
    (hadvance : σ (j + n) - σ j ≤ d)
    (hstart : a ≤ L - ⌈σ j⌉) (hcoarse : L - ⌈σ k⌉ ≤ B)
    (hgap : (B : ℝ) < (a : ℝ) - d - 1) : j + n < k := by
  have hb : (B : ℝ) < (L : ℝ) - (⌈σ (j + n)⌉ : ℝ) := by
    have hs : (a : ℝ) ≤ (L : ℝ) - (⌈σ j⌉ : ℝ) := by exact_mod_cast hstart
    linarith [ceiling_increment (σ j) (σ (j + n))]
  by_contra h
  have hm := Int.ceil_mono (hσ (Nat.le_of_not_gt h))
  have hc : (L : ℝ) - (⌈σ k⌉ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hcoarse
  have hm' : (⌈σ k⌉ : ℝ) ≤ (⌈σ (j + n)⌉ : ℝ) := by exact_mod_cast hm
  linarith

theorem multiples_disjoint {n j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Finset.Ico (j * n) (j * n + n)) (Finset.Ico (k * n) (k * n + n)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨hja, haj⟩ := Finset.mem_Ico.mp ha
  obtain ⟨hka, hak⟩ := Finset.mem_Ico.mp hb
  rcases lt_or_gt_of_ne hjk with h | h
  · have hle := Nat.mul_le_mul_right n h
    have : j * n + n ≤ k * n := by simpa [Nat.add_mul] using hle
    omega
  · have hle := Nat.mul_le_mul_right n h
    have : k * n + n ≤ j * n := by simpa [Nat.add_mul] using hle
    omega

theorem sum_disjoint_drops_le {α : Type uα} (s : Finset α) (u v : α → ℕ)
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Finset.Ico (u i) (v i)))
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, (g (u i) - g (v i)) ≤ g 0 := by
  classical
  let N := s.sup v
  have htel : ∀ i ∈ s, g (u i) - g (v i) =
      ∑ t ∈ Finset.Ico (u i) (v i), (g t - g (t + 1)) := by
    intro i hi
    have ht := Finset.sum_Ico_sub (fun t => -g t) (huv i hi)
    simpa only [neg_sub_neg] using ht.symm
  simp_rw [Finset.sum_congr rfl htel]
  rw [← Finset.sum_biUnion hd]
  calc
    ∑ t ∈ s.biUnion (fun i => Finset.Ico (u i) (v i)), (g t - g (t + 1)) ≤
        ∑ t ∈ Finset.range N, (g t - g (t + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨i, hi, hit⟩ := Finset.mem_biUnion.mp ht
        exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hit).2.trans_le (Finset.le_sup hi))
      · intro t _ _
        exact sub_nonneg.mpr (hg (Nat.le_succ t))
    _ = g 0 - g N := by
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun t => -g t) N
    _ ≤ g 0 := sub_le_self _ (hgn N)

end Windows

end EntropyRateDimension

end

end OAI
