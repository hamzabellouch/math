import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

section Grouping
variable {ι κ : Type*} [DecidableEq κ]

def groupedValue (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) (t : κ) : ℂ :=
  ∑ i ∈ s with tag i = t, f i

def diagonalComplex (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, if tag j = tag i then f i * conj (f j) else 0

def offDiagonalComplex (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, if tag j ≠ tag i then f i * conj (f j) else 0

theorem diagonal_add_offDiagonal (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) :
    diagonalComplex s tag f + offDiagonalComplex s tag f =
      (∑ i ∈ s, f i) * conj (∑ i ∈ s, f i) := by
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [diagonalComplex, offDiagonalComplex, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : tag j = tag i <;> simp [h]

theorem diagonal_eq_grouped_squares (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) :
    diagonalComplex s tag f =
      ∑ t ∈ s.image tag, (‖groupedValue s tag f t‖^2 : ℝ) := by
  have hfirst : diagonalComplex s tag f =
      ∑ i ∈ s, f i * conj (groupedValue s tag f (tag i)) := by
    simp only [diagonalComplex, groupedValue, map_sum, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : tag j = tag i <;> simp only [h, ite_true, ite_false, map_zero, mul_zero]
  rw [hfirst, Complex.ofReal_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image tag) (g := tag)
    (fun i hi => Finset.mem_image_of_mem tag hi)]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ i ∈ s with tag i = t, f i * conj (groupedValue s tag f (tag i))) =
        ∑ i ∈ s with tag i = t, f i * conj (groupedValue s tag f t) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = groupedValue s tag f t * conj (groupedValue s tag f t) := by
      rw [← Finset.sum_mul]
      rfl
    _ = (‖groupedValue s tag f t‖^2 : ℝ) := by
      simpa only [Complex.ofReal_pow] using Complex.mul_conj' (groupedValue s tag f t)

theorem diagonal_nonneg (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) :
    0 ≤ (diagonalComplex s tag f).re := by
  rw [diagonal_eq_grouped_squares]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem diagonal_real (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) :
    (diagonalComplex s tag f).im = 0 := by
  rw [diagonal_eq_grouped_squares]
  exact Complex.ofReal_im _

theorem offDiagonal_real (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) :
    (offDiagonalComplex s tag f).im = 0 := by
  have h := congrArg Complex.im (diagonal_add_offDiagonal s tag f)
  rw [Complex.mul_conj', ← Complex.ofReal_pow] at h
  simpa only [Complex.add_im, diagonal_real s tag f, Complex.ofReal_im, zero_add] using h

theorem square_split (s : Finset ι) (tag : ι → κ) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖^2 =
      (diagonalComplex s tag f).re + (offDiagonalComplex s tag f).re := by
  have h := congrArg Complex.re (diagonal_add_offDiagonal s tag f)
  rw [Complex.mul_conj', ← Complex.ofReal_pow] at h
  simpa only [Complex.add_re, Complex.ofReal_re] using h.symm

end Grouping

theorem ratio_tag_eq_iff {v w Hplus Hminus : ℚ}
    (hplus : Hplus ≠ 0) (hminus : Hminus ≠ 0) :
    v / Hplus = w / Hminus ↔ v * Hminus = w * Hplus :=
  div_eq_div_iff hplus hminus

end Ostmann.Construction

end

end OAI
