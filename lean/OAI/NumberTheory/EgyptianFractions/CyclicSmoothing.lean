import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- Convolution of a normalized nonnegative kernel with an interval (or any
finite window). -/
def window {G : Type*} [AddGroup G] (K : G → ℝ) (J : Finset G) (x : G) : ℝ :=
  ∑ y ∈ J, K (x - y)

lemma window_nonneg {G : Type*} [AddGroup G] (K : G → ℝ) (J : Finset G)
    (hK : ∀ x, 0 ≤ K x) (x : G) : 0 ≤ window K J x :=
  Finset.sum_nonneg (fun _ _ => hK _)

lemma window_le_one {G : Type*} [AddCommGroup G] [Fintype G]
    (K : G → ℝ) (J : Finset G) (hK : ∀ x, 0 ≤ K x) (hmass : ∑ x, K x = 1)
    (x : G) : window K J x ≤ 1 := by
  calc
    window K J x ≤ ∑ y, K (x - y) := Finset.sum_le_univ_sum_of_nonneg (fun _ => hK _)
    _ = ∑ y, K y := (Equiv.subLeft x).sum_comp K
    _ = 1 := hmass

lemma sum_window {G : Type*} [AddCommGroup G] [Fintype G]
    (K : G → ℝ) (J : Finset G) (hmass : ∑ x, K x = 1) :
    (∑ x, window K J x) = (J.card : ℝ) := by
  simp only [window]
  rw [Finset.sum_comm]
  have hshift (y : G) : (∑ x, K (x - y)) = 1 := by
    calc
      (∑ x, K (x - y)) = ∑ x, K x := (Equiv.subRight y).sum_comp K
      _ = 1 := hmass
  simp_rw [hshift]
  simp

lemma window_le_of_kernel_bound {G : Type*} [AddGroup G]
    (K : G → ℝ) (J : Finset G) (x : G) (η : ℝ)
    (h : ∀ y ∈ J, K (x - y) ≤ η) : window K J x ≤ (J.card : ℝ) * η := by
  calc
    window K J x ≤ ∑ _y ∈ J, η := Finset.sum_le_sum h
    _ = (J.card : ℝ) * η := by simp

/-- The counting conclusion of the smoothing argument. The spectral input is
only the sampled mean lower bound; the geometric input is the kernel tail
bound outside the outer window. Repeated sample values are allowed. -/
theorem count_window_lower {G Ω : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (K : G → ℝ) (inner outer : Finset G) (samples : Finset Ω) (x : Ω → G)
    (E η : ℝ) (hK : ∀ y, 0 ≤ K y) (hmass : ∑ y, K y = 1) (hη : 0 ≤ η)
    (htail : ∀ z, z ∉ outer → ∀ y ∈ inner, K (z - y) ≤ η)
    (hmean : (samples.card : ℝ) * ((inner.card : ℝ) / Fintype.card G - E) ≤
      ∑ ω ∈ samples, window K inner (x ω)) :
    (samples.card : ℝ) * ((inner.card : ℝ) / Fintype.card G - E -
      (inner.card : ℝ) * η) ≤ ((samples.filter (fun ω => x ω ∈ outer)).card : ℝ) := by
  classical
  have hbound (ω : Ω) : window K inner (x ω) ≤
      (if x ω ∈ outer then (1 : ℝ) else 0) + (inner.card : ℝ) * η := by
    split_ifs with h
    · have hu := window_le_one K inner hK hmass (x ω)
      have hp : 0 ≤ (inner.card : ℝ) * η := by positivity
      linarith
    · simpa using window_le_of_kernel_bound K inner (x ω) η (htail _ h)
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ samples) => hbound ω)
  have hind : (∑ ω ∈ samples, if x ω ∈ outer then (1 : ℝ) else 0) =
      ((samples.filter (fun ω => x ω ∈ outer)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, hind] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

end Problem337.CyclicSmoothing

end

end OAI
