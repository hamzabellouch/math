import OAI.Combinatorics.BinaryEdit.SegmentCodeEstimates
import OAI.Combinatorics.BinaryEdit.SegmentMatchingCount
import OAI.Combinatorics.BinaryEdit.CodeUnionBound

namespace OAI

/-!
Finite probabilistic construction of a codebook simultaneously separating every
long segment of every pair of differently labelled blocks. Counting is done on
all Boolean codebooks, so no randomness or existence hypothesis is retained.
-/

namespace TreeEdit.BinaryLower.SegmentCode

open RandomMatching CodeUnionBound

/-- A contiguous window of positions in a block. -/
def window {P : ℕ} (a i : ℕ) (h : i+a ≤ P) : Fin a → Fin P :=
  fun t => ⟨i+t.val, by have := t.isLt; omega⟩

theorem window_injective {P : ℕ} (a i : ℕ) (h : i+a ≤ P) :
    Function.Injective (window a i h) := by
  intro t u he
  apply Fin.ext
  have he' := congrArg Fin.val he
  dsimp [window] at he'
  omega

/-- Segment separation in terms of increasing position lists. -/
def SegmentSeparated {K P : ℕ} (c : Fin K → Fin P → Bool) (a₀ : ℕ) : Prop :=
  ∀ (k l : Fin K), k ≠ l → ∀ (a i j : ℕ), a₀ ≤ a →
    ∀ (hi : i+a ≤ P) (hj : j+a ≤ P) (s : ℕ)
      (f g : IncreasingPositions a s),
      (∀ t, c k (window a i hi (f.1 t)) = c l (window a j hj (g.1 t))) →
        100*s ≤ 99*a

/-- Bad comparisons include only valid windows longer than the cutoff. -/
noncomputable def comparisonBad {K P : ℕ} (a₀ : ℕ)
    (t : SegmentComparison K (P+1)) : Finset (Fin K → Fin P → Bool) := by
  classical
  rcases t with ⟨k, l, a, i, j⟩
  exact if h : k ≠ l ∧ a₀ ≤ a.val ∧ i.val+a.val ≤ P ∧ j.val+a.val ≤ P then
    segmentMatchingEvent (a.val-a.val/100) k l
      (window a.val i.val h.2.2.1) (window a.val j.val h.2.2.2)
  else ∅

/-- Each valid comparison has exponentially small bad-event frequency. -/
theorem comparisonBad_fraction_le {K P : ℕ} (a₀ : ℕ)
    (t : SegmentComparison K (P+1)) :
    ((comparisonBad a₀ t).card : ℝ) / Fintype.card (Fin K → Fin P → Bool) ≤
      (9/10 : ℝ)^a₀ := by
  classical
  rcases t with ⟨k, l, a, i, j⟩
  dsimp only [comparisonBad]
  split_ifs with h
  · have hc : Fintype.card (Fin K → Fin P → Bool) = 2^(K*P) := by
      simp [← pow_mul, Nat.mul_comm]
    rw [hc]
    push_cast
    have hs : a.val-a.val/100 ≤ a.val := Nat.sub_le _ _
    have hlarge : 99*a.val ≤ 100*(a.val-a.val/100) := by omega
    have hbin := nearly_full_matching_bound a.val (a.val-a.val/100) hs hlarge
    have hbin' : ((a.val.choose (a.val-a.val/100) : ℝ)^2) /
        (2 : ℝ)^(a.val-a.val/100) ≤ (9/10 : ℝ)^a.val := by
      simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using hbin
    calc
      _ ≤ ((a.val.choose (a.val-a.val/100) : ℝ)^2) /
          (2 : ℝ)^(a.val-a.val/100) :=
        segmentMatchingEvent_fraction_le k l h.1 _ _
          (window_injective _ _ _) hs
      _ ≤ (9/10 : ℝ)^a.val := hbin'
      _ ≤ (9/10 : ℝ)^a₀ := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h.2.1
  · simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/-- A finite numerical union-bound criterion produces one codebook that works
for every pair of labels, every valid pair of windows, and every matching. -/
theorem exists_segmentSeparated (K P a₀ : ℕ)
    (hprob : (K : ℝ)^2 * ((P+1 : ℕ) : ℝ)^3 * (9/10 : ℝ)^a₀ < 1) :
    ∃ c : Fin K → Fin P → Bool, SegmentSeparated c a₀ := by
  classical
  have hsum : (Fintype.card (SegmentComparison K (P+1)) : ℝ) *
      (9/10 : ℝ)^a₀ < 1 := by
    simpa only [card_segmentComparison, Nat.cast_mul, Nat.cast_pow] using hprob
  obtain ⟨c, hc⟩ := exists_avoiding_of_uniform_probability_bound
    (comparisonBad (K := K) (P := P) a₀) ((9/10 : ℝ)^a₀)
    (comparisonBad_fraction_le a₀) hsum
  refine ⟨c, ?_⟩
  intro k l hkl a i j ha hi hj r f g heq
  by_contra hn
  have hs : a-a/100 ≤ r := by omega
  let fs : IncreasingPositions a (a-a/100) :=
    ⟨fun t => f.1 (Fin.castLE hs t), f.2.comp (Fin.strictMono_castLE hs)⟩
  let gs : IncreasingPositions a (a-a/100) :=
    ⟨fun t => g.1 (Fin.castLE hs t), g.2.comp (Fin.strictMono_castLE hs)⟩
  let t : SegmentComparison K (P+1) :=
    (k, l, ⟨a, by omega⟩, ⟨i, by omega⟩, ⟨j, by omega⟩)
  apply hc t
  dsimp [t, comparisonBad]
  rw [dite_eq_left ⟨hkl, ha, hi, hj⟩]
  simp only [segmentMatchingEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fs, gs, fun u => heq (Fin.castLE hs u)⟩

end TreeEdit.BinaryLower.SegmentCode

end OAI
