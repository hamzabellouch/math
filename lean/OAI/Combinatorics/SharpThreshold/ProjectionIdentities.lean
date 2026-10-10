import Mathlib

namespace OAI

universe u v

noncomputable section

namespace Problem313.WeightedProjection

open scoped BigOperators

variable {ι : Type u} {X : Type v} [Fintype X]

def coefficient (w : X → ℝ) (basis : ι → X → ℝ) (f : X → ℝ) (i : ι) : ℝ :=
  ∑ x, w x * f x * basis i x

def synthesis (basis : ι → X → ℝ) (L : Finset ι) (c : ι → ℝ) (x : X) : ℝ :=
  ∑ i ∈ L, c i * basis i x

/-- Pairing a function with a finite spectral expansion pairs its coefficients. -/
theorem inner_synthesis (w : X → ℝ) (basis : ι → X → ℝ)
    (f : X → ℝ) (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * f x * synthesis basis L c x) =
      ∑ i ∈ L, c i * coefficient w basis f i := by
  simp only [synthesis, coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Orthonormality computes the coefficient of a finite spectral expansion. -/
theorem coefficient_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) (i : ι) :
    coefficient w basis (synthesis basis L c) i = if i ∈ L then c i else 0 := by
  unfold coefficient synthesis
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (j : ι) :
      (∑ x, w x * (c j * basis j x) * basis i x) =
        c j * (if j = i then 1 else 0) := by
    rw [← horth j i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp only [hterm]
  simp

/-- The squared norm of a finite orthonormal expansion is its coefficient energy. -/
theorem second_moment_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * (synthesis basis L c x) ^ 2) = ∑ i ∈ L, (c i) ^ 2 := by
  have hid := inner_synthesis w basis (synthesis basis L c) L c
  simp only [coefficient_synthesis w basis horth] at hid
  calc
    (∑ x, w x * (synthesis basis L c x) ^ 2) =
        ∑ x, w x * synthesis basis L c x * synthesis basis L c x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ i ∈ L, c i * (if i ∈ L then c i else 0) := hid
    _ = ∑ i ∈ L, (c i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi, pow_two]

/-- A spectral projection has the same inner product with the original function
as its squared norm. -/
theorem inner_projection (w : X → ℝ) (basis : ι → X → ℝ)
    (f : X → ℝ) (L : Finset ι) :
    (∑ x, w x * f x * synthesis basis L (coefficient w basis f) x) =
      ∑ i ∈ L, (coefficient w basis f i) ^ 2 := by
  rw [inner_synthesis]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Problem313.WeightedProjection

end

end OAI
