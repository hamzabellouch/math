import Mathlib
import OAI.Combinatorics.KMedian.Reduction.NormalizationGuesses

namespace OAI

section
section
namespace MetricKMedian.Normalization
open Finset
variable {m n : ℕ}

def matrixGuesses (d : Fin m → Fin n → ℚ) : Finset ℚ :=
  (univ : Finset (Fin m × Fin n)).biUnion (fun a =>
    if 0 < d a.1 a.2 then
      (range (m.size+1)).image (fun t => d a.1 a.2*(2:ℚ)^t)
    else ∅)

theorem matrixGuesses_pos (d : Fin m → Fin n → ℚ) (B : ℚ)
    (hB : B ∈ matrixGuesses d) : 0 < B := by
  obtain ⟨a,_,ha⟩ := mem_biUnion.mp hB
  split_ifs at ha with h
  · obtain ⟨t,_,rfl⟩ := mem_image.mp ha
    exact mul_pos h (by positivity)
  · exact False.elim (notMem_empty _ ha)

theorem matrixGuesses_card (d : Fin m → Fin n → ℚ) :
    (matrixGuesses d).card ≤ m*n*(m.size+1) := by
  calc
    _ ≤ ∑ a : Fin m × Fin n,
        (if 0 < d a.1 a.2 then
          (range (m.size+1)).image (fun t => d a.1 a.2*(2:ℚ)^t)
          else ∅).card := card_biUnion_le
    _ ≤ ∑ _a : Fin m × Fin n, (m.size+1) := by
      apply sum_le_sum
      intro a _
      split_ifs
      · exact card_image_le.trans (card_range _).le
      · simp only [card_empty]; omega
    _ = _ := by simp

theorem matrixGoodGuess (d : Fin m → Fin n → ℚ) (hd : ∀ j i, 0 ≤ d j i)
    (a : Fin m → Fin n) (hc : 0 < ∑ j, d j (a j)) :
    ∃ B ∈ matrixGuesses d, 0 < B ∧
      1/2 ≤ (∑ j, d j (a j))/B ∧ (∑ j, d j (a j))/B ≤ 1 := by
  have hJ : (univ : Finset (Fin m)).Nonempty := by
    by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    rw [he,sum_empty] at hc
    exact lt_irrefl 0 hc
  let A := univ.image (fun j => d j (a j))
  have hA : A.Nonempty := hJ.image _
  obtain ⟨j,_,he⟩ := mem_image.mp (max'_mem A hA)
  have hmax : ∀ b : Fin m, d b (a b) ≤ d j (a j) := by
    intro b
    rw [he]
    exact le_max' A _ (mem_image_of_mem _ (mem_univ b))
  have hupper : (∑ b, d b (a b)) ≤ (m:ℚ)*d j (a j) := by
    calc
      _ ≤ ∑ _b : Fin m, d j (a j) := sum_le_sum (fun b _ => hmax b)
      _ = _ := by simp
  have hpos : 0 < d j (a j) := by
    by_contra h
    have hz : d j (a j)=0 := le_antisymm (le_of_not_gt h) (hd j (a j))
    rw [hz,mul_zero] at hupper
    exact (not_lt_of_ge hupper) hc
  have hl : d j (a j) ≤ ∑ b, d b (a b) :=
    single_le_sum (fun b _ => hd b (a b)) (mem_univ j)
  have hn : (m:ℚ) ≤ (2:ℚ)^m.size := by
    exact_mod_cast ((Nat.size_le).mp (le_refl m.size)).le
  have hcu : (∑ b, d b (a b)) ≤ d j (a j)*(2:ℚ)^m.size :=
    hupper.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn hpos.le])
  obtain ⟨t,ht,h1,h2⟩ := dyadic_bracket _ _ m.size hpos hl hcu
  let B := d j (a j)*(2:ℚ)^t
  have hB : 0 < B := mul_pos hpos (by positivity)
  refine ⟨B,mem_biUnion.mpr ⟨(j,a j),mem_univ _,?_⟩,hB,?_,?_⟩
  · simp only [ite_eq_left hpos]
    exact mem_image.mpr ⟨t,mem_range.mpr (by omega),rfl⟩
  · apply (le_div_iff₀ hB).mpr
    change 1/2*B ≤ _
    change B ≤ 2*(∑ b, d b (a b)) at h2
    linarith
  · exact (div_le_one hB).mpr h1

end MetricKMedian.Normalization
end
end

end OAI
