import Mathlib

namespace OAI

universe u v

/-!
# Averaging and capture of nonnegative spectral mass

For any finite family of nonnegative masses and random detection events,
if every low-degree support is detected with probability at least `a`, an
upper bound on the average detected mass bounds the low-degree mass.
-/

namespace Problem313

open scoped BigOperators

section FiniteCapture

variable {ι : Type u} {β : Type v} [Fintype ι] [Fintype β]

/-- Interchange averaging over blocks and summing the mass of captured supports. -/
theorem weighted_capture_sum_swap
    (w : β → ℝ) (mass : ι → ℝ) (detect : β → ι → Prop)
    [DecidableRel detect] :
    (∑ b, w b * ∑ i, if detect b i then mass i else 0) =
      ∑ i, (∑ b, if detect b i then w b else 0) * mass i := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

/-- A pointwise detection lower bound controls the mass on any chosen finite set. -/
theorem capture_mass_mul_le
    (low : Finset ι) (mass detection : ι → ℝ) (a : ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hdet : ∀ i, 0 ≤ detection i)
    (hlow : ∀ i ∈ low, a ≤ detection i) :
    a * ∑ i ∈ low, mass i ≤ ∑ i, detection i * mass i := by
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ low, a * mass i ≤ ∑ i ∈ low, detection i * mass i := by
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hlow i hi) (hmass i)
    _ ≤ ∑ i, detection i * mass i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
        (fun i hi hnot => mul_nonneg (hdet i) (hmass i))

/-- The same capture inequality stated directly with finite block averaging. -/
theorem averaged_capture_mass_mul_le
    (low : Finset ι) (w : β → ℝ) (mass : ι → ℝ)
    (detect : β → ι → Prop) [DecidableRel detect] (a : ℝ)
    (hw : ∀ b, 0 ≤ w b) (hmass : ∀ i, 0 ≤ mass i)
    (hlow : ∀ i ∈ low, a ≤ ∑ b, if detect b i then w b else 0) :
    a * ∑ i ∈ low, mass i ≤
      ∑ b, w b * ∑ i, if detect b i then mass i else 0 := by
  rw [weighted_capture_sum_swap]
  apply capture_mass_mul_le low mass _ a hmass
  · intro i
    apply Finset.sum_nonneg
    intro b hb
    split_ifs
    · exact hw b
    · exact le_rfl
  · exact hlow

/-- Cancel the random-block detection factor. The factor `4` is exactly the
ratio between the edge-touch upper bound `2*m/n` and detection `m/(2*n)`. -/
theorem block_capture_mass_le
    (low : Finset ι) (w : β → ℝ) (mass : ι → ℝ)
    (detect : β → ι → Prop) [DecidableRel detect]
    (m n Q : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hw : ∀ b, 0 ≤ w b) (hmass : ∀ i, 0 ≤ mass i)
    (hlow : ∀ i ∈ low, m / (2 * n) ≤ ∑ b, if detect b i then w b else 0)
    (haverage : (∑ b, w b * ∑ i, if detect b i then mass i else 0) ≤
      (2 * m / n) * Q) :
    (∑ i ∈ low, mass i) ≤ 4 * Q := by
  have ha : 0 < m / (2 * n) := div_pos hm (mul_pos (by norm_num) hn)
  have h := (averaged_capture_mass_mul_le low w mass detect (m / (2 * n))
    hw hmass hlow).trans haverage
  have heq : (2 * m / n) * Q = (m / (2 * n)) * (4 * Q) := by ring
  rw [heq] at h
  exact (mul_le_mul_iff_right₀ ha).mp h

end FiniteCapture

end Problem313

end OAI
