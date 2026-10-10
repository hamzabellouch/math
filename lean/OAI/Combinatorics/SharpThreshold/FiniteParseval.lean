import Mathlib

namespace OAI

universe u v

noncomputable section

namespace Problem313.FiniteParseval

open Finset Matrix

variable {α : Type u} {Ω : Type v} [Fintype α] [Fintype Ω] [DecidableEq α] [DecidableEq Ω]

/-- Fourier coefficient for an arbitrary finite weighted system. -/
def coefficient (w : Ω → ℝ) (χ : α → Ω → ℝ) (f : Ω → ℝ) (a : α) : ℝ :=
  ∑ x, w x * f x * χ a x

/-- A square weighted orthonormal system is complete. No positivity is needed
for this algebraic statement. -/
theorem expansion (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (hcard : Fintype.card α = Fintype.card Ω)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f : Ω → ℝ) (x : Ω) :
    (∑ a, coefficient w χ f a * χ a x) = f x := by
  let A : Matrix α Ω ℝ := fun a x => w x * χ a x
  let B : Matrix Ω α ℝ := fun x a => χ a x
  have hAB : A * B = 1 := by
    ext a b
    change (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0
    exact horth a b
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hAB
  have hAf : A *ᵥ f = fun a => coefficient w χ f a := by
    funext a
    simp only [Matrix.mulVec, dotProduct, A, coefficient]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  calc
    (∑ a, coefficient w χ f a * χ a x) = (B *ᵥ (A *ᵥ f)) x := by
      rw [hAf]
      simp only [Matrix.mulVec, dotProduct, B]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = f x := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]

/-- Parseval's bilinear identity for a finite weighted orthonormal system. -/
theorem parseval_bilinear (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (hcard : Fintype.card α = Fintype.card Ω)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f g : Ω → ℝ) :
    (∑ a, coefficient w χ f a * coefficient w χ g a) = ∑ x, w x * f x * g x := by
  simp only [coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ a, (∑ y, w y * f y * χ a y) * (w x * g x * χ a x)) =
        w x * g x * (∑ a, coefficient w χ f a * χ a x) := by
      simp only [Finset.mul_sum, coefficient]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = w x * f x * g x := by rw [expansion w χ hcard horth]; ring

/-- The usual sum-of-squares Parseval identity. -/
theorem parseval (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (hcard : Fintype.card α = Fintype.card Ω)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f : Ω → ℝ) :
    (∑ a, (coefficient w χ f a)^2) = ∑ x, w x * (f x)^2 := by
  simpa only [pow_two, mul_assoc] using parseval_bilinear w χ hcard horth f f

/-- Synthesis using only a selected finite set of spectral coordinates. -/
def synthesis (χ : α → Ω → ℝ) (c : α → ℝ) (s : Finset α) (x : Ω) : ℝ :=
  ∑ a ∈ s, c a * χ a x

omit [Fintype α] [DecidableEq Ω] in
theorem coefficient_synthesis (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (c : α → ℝ) (s : Finset α) (a : α) :
    coefficient w χ (synthesis χ c s) a = if a ∈ s then c a else 0 := by
  unfold coefficient synthesis
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ b ∈ s, ∑ x, w x * (c b * χ b x) * χ a x) =
        ∑ b ∈ s, c b * (∑ x, w x * χ b x * χ a x) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = if a ∈ s then c a else 0 := by simp_rw [horth]; simp

omit [Fintype α] [DecidableEq α] [DecidableEq Ω] in
theorem inner_synthesis (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (f : Ω → ℝ) (c : α → ℝ) (s : Finset α) :
    (∑ x, w x * f x * synthesis χ c s x) =
      ∑ a ∈ s, c a * coefficient w χ f a := by
  simp only [synthesis, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

omit [Fintype α] [DecidableEq Ω] in
theorem synthesis_sq (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (c : α → ℝ) (s : Finset α) :
    (∑ x, w x * (synthesis χ c s x)^2) = ∑ a ∈ s, (c a)^2 := by
  calc
    (∑ x, w x * (synthesis χ c s x)^2) =
        ∑ x, w x * synthesis χ c s x * synthesis χ c s x := by
      simp only [pow_two, mul_assoc]
    _ = ∑ a ∈ s, c a * coefficient w χ (synthesis χ c s) a :=
      inner_synthesis w χ (synthesis χ c s) c s
    _ = ∑ a ∈ s, (c a)^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [coefficient_synthesis w χ horth, ite_eq_left ha, pow_two]

omit [Fintype α] [DecidableEq Ω] in
/-- The algebraic orthogonal-projection identity used by the low-degree
Hölder estimate. -/
theorem projection_inner_eq_sq (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f : Ω → ℝ) (s : Finset α) :
    (∑ x, w x * f x * synthesis χ (coefficient w χ f) s x) =
      ∑ x, w x * (synthesis χ (coefficient w χ f) s x)^2 := by
  rw [inner_synthesis, synthesis_sq w χ horth]
  simp only [pow_two]

end Problem313.FiniteParseval

end

end OAI
