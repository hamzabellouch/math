import Mathlib
import OAI.Combinatorics.KMedian.Optimization.TruncatedObjective

namespace OAI

section
section
namespace MetricKMedian.RationalGrid
open Finset

def At (D : ℤ) (q : ℚ) : Prop := ∃ a : ℤ, q=(a:ℚ)/(D:ℚ)

theorem zero (D : ℤ) : At D 0 := ⟨0,by simp⟩

theorem integer (D a : ℤ) (hD : D ≠ 0) : At D (a:ℚ) := by
  refine ⟨a*D,?_⟩
  rw [Int.cast_mul,mul_div_cancel_right₀ _ (by exact_mod_cast hD)]

theorem sub {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (a-b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A-B,by rw [Int.cast_sub,sub_div]⟩

theorem neg {D : ℤ} {a : ℚ} (ha : At D a) : At D (-a) := by
  obtain ⟨A,rfl⟩ := ha
  exact ⟨-A,by rw [Int.cast_neg]; ring⟩

theorem max {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

theorem sum {ι : Type} (U : Finset ι) (f : ι → ℚ) (D : ℤ)
    (h : ∀ i ∈ U, At D (f i)) : At D (∑ i ∈ U, f i) := by
  classical
  choose A hA using (fun i : U => h i.val i.property)
  refine ⟨∑ i : U, A i,?_⟩
  rw [Int.cast_sum,sum_div]
  simp_rw [← hA]
  exact (sum_coe_sort U f).symm

end MetricKMedian.RationalGrid

namespace MetricKMedian.TruncatedLP
open Finset RationalGrid
variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem truncated_grid (d : κ → ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ j i, At D (d j i)) (j : κ) (i : ι) : At D (truncated d H j i) := by
  unfold truncated
  split_ifs
  · exact hd j i
  · exact RationalGrid.integer D H hD

theorem threshold_grid (d y : ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ i, At D (d i)) : At D (FractionalDual.bestThreshold d y H) := by
  have hh := (FractionalDual.bestThreshold_spec d y H).1
  obtain he | hh := mem_insert.mp hh
  · rw [he]; exact RationalGrid.zero D
  · obtain he | hh := mem_insert.mp hh
    · rw [he]; exact RationalGrid.integer D H hD
    · obtain ⟨i,_,he⟩ := mem_image.mp hh
      rw [← he]
      exact hd i

theorem gradient_grid (d : κ → ι → ℚ) (y : ι → ℚ) (D H : ℤ) (hD : D ≠ 0)
    (hd : ∀ j i, At D (d j i)) (i : ι) : At D (gradient d y H i) := by
  apply RationalGrid.sum
  intro j _
  unfold FractionalDual.gradient
  exact RationalGrid.neg (RationalGrid.max (RationalGrid.zero D)
    (RationalGrid.sub (threshold_grid _ _ D H hD (truncated_grid d D H hD hd j))
      (truncated_grid d D H hD hd j i)))

end MetricKMedian.TruncatedLP
end
end

end OAI
