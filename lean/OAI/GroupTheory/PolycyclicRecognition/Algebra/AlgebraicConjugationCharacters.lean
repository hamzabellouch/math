import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialConjugationSpectrum
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

namespace OAI

/-! # Algebraic conjugation characters are roots of unity

The word count bounds every complex embedding of the eigenvalue. Kronecker's
theorem then applies to an integral eigenvalue in a number field.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G K : Type*} [Group G] [DecidableEq G] [Field K] [NumberField K]

theorem polynomial_growth_algebraic_conjugation_character_torsion
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (x : N)
    (χ : N →* Multiplicative K) (z : K) (hz : IsIntegral ℤ z)
    (hχ : ∀ y, (χ (MulAut.conjNormal t y)).toAdd = z * (χ y).toAdd)
    (hxχ : (χ x).toAdd ≠ 0) : ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  suffices hh : ∀ φ : K →+* ℂ, ‖φ z‖ = 1 by
    obtain ⟨n, hn, he⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hz hh
    exact ⟨n, hn, he⟩
  intro φ
  let ψ : N →* Multiplicative ℂ := φ.toAddMonoidHom.toMultiplicative.comp χ
  have hψ (y : N) : (ψ y).toAdd = φ (χ y).toAdd := rfl
  have hψconj (y : N) :
      (ψ (MulAut.conjNormal t y)).toAdd = φ z * (ψ y).toAdd := by
    simp only [hψ, hχ, map_mul]
  have hxψ : (ψ x).toAdd ≠ 0 := by
    rw [hψ]
    intro h
    exact hxχ (φ.injective (h.trans (map_zero φ).symm))
  exact polynomial_growth_conjugation_character_norm_eq_one S hS hgen hvol N t x
    ψ (φ z) hψconj hxψ

end PolycyclicRecognition

end

end OAI
