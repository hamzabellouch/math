import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExpandingConjugationWords

namespace OAI

/-! # Unit-modulus conjugation characters in polynomial-growth groups

Apply the short-word count to powers of the conjugating element and then to
its inverse. Every nonzero scalar character of this action has modulus one.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G]

omit [DecidableEq G] in
theorem conjugation_character_pow (N : Subgroup G) [N.Normal]
    (t : G) (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (MulAut.conjNormal t y)).toAdd = z * (χ y).toAdd)
    (k : ℕ) (y : N) :
    (χ (MulAut.conjNormal (t ^ k) y)).toAdd = z ^ k * (χ y).toAdd := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, map_mul, MulAut.mul_apply, ih, hχ, pow_succ]
    ring

theorem polynomial_growth_conjugation_character_norm_le_one
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (x : N)
    (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (MulAut.conjNormal t y)).toAdd = z * (χ y).toAdd)
    (hxχ : (χ x).toAdd ≠ 0) : ‖z‖ ≤ 1 := by
  by_contra! hz
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 : ℝ) hz
  have hb := polynomial_growth_no_expanding_conjugation S hS hgen hvol N (t ^ k) x
    χ (z ^ k) (conjugation_character_pow N t χ z hχ k) hxχ
  rw [norm_pow] at hb
  linarith

theorem polynomial_growth_conjugation_character_norm_eq_one
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (x : N)
    (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (MulAut.conjNormal t y)).toAdd = z * (χ y).toAdd)
    (hxχ : (χ x).toAdd ≠ 0) : ‖z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    intro hz
    have h := hχ ((MulAut.conjNormal t)⁻¹ x)
    rw [MulAut.apply_inv_self, hz, zero_mul] at h
    exact hxχ h
  have hinv (y : N) :
      (χ (MulAut.conjNormal t⁻¹ y)).toAdd = z⁻¹ * (χ y).toAdd := by
    have h := hχ (MulAut.conjNormal t⁻¹ y)
    rw [map_inv, MulAut.apply_inv_self] at h
    calc
      _ = z⁻¹ * (z * (χ (MulAut.conjNormal t⁻¹ y)).toAdd) := by
        rw [← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
      _ = _ := congrArg (z⁻¹ * ·) h.symm
  have hu := polynomial_growth_conjugation_character_norm_le_one
    S hS hgen hvol N t x χ z hχ hxχ
  have hl := polynomial_growth_conjugation_character_norm_le_one
    S hS hgen hvol N t⁻¹ x χ z⁻¹ hinv hxχ
  rw [norm_inv] at hl
  exact le_antisymm hu ((inv_le_one₀ (norm_pos_iff.mpr hz0)).mp hl)

end PolycyclicRecognition

end

end OAI
