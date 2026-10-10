import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraicExpandingEmbedding
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

namespace OAI

/-! # An expanding place for a nontorsion algebraic number

If all finite-place norms are at most one, the element is an algebraic
integer. Kronecker's theorem then supplies an expanding complex embedding
unless the element is a root of unity.
-/

noncomputable section
namespace PolycyclicRecognition
open NumberField IsDedekindDomain

theorem nonintegral_has_expanding_finite_place
    {K : Type*} [Field K] [NumberField K] (z : K)
    (hi : ¬ IsIntegral ℤ z) :
    ∃ v : HeightOneSpectrum (𝓞 K), 1 < ‖FinitePlace.embedding v z‖ := by
  by_contra! h
  have hv (v : HeightOneSpectrum (𝓞 K)) : v.valuation K z ≤ 1 := by
    have hh := h v
    rw [FinitePlace.norm_embedding'] at hh
    have hn : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (v.valuation K z) ≤ 1 := by exact_mod_cast hh
    exact (WithZeroMulInt.toNNReal_le_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp hn
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K z hv
  apply hi
  rw [← ha]
  exact a.property

theorem nontorsion_numberField_expanding_place
    {K : Type*} [Field K] [NumberField K] (z : K) (hz : z ≠ 0)
    (hnt : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) :
    (∃ σ : K →+* ℂ, 1 < ‖σ z‖) ∨
      ∃ v : HeightOneSpectrum (𝓞 K), 1 < ‖FinitePlace.embedding v z‖ := by
  by_cases hi : IsIntegral ℤ z
  · exact Or.inl (integral_nontorsion_has_expanding_complex_embedding z hz hi hnt)
  · exact Or.inr (nonintegral_has_expanding_finite_place z hi)

theorem nontorsion_numberField_expanding_absoluteValue
    {K : Type*} [Field K] [NumberField K] (z : K) (hz : z ≠ 0)
    (hnt : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) :
    ∃ v : AbsoluteValue K ℝ, 1 < v z := by
  obtain h | h := nontorsion_numberField_expanding_place z hz hnt
  · obtain ⟨σ, hσ⟩ := h
    exact ⟨NumberField.place σ, hσ⟩
  · obtain ⟨v, hv⟩ := h
    exact ⟨HeightOneSpectrum.adicAbv K v, by simpa only [FinitePlace.norm_embedding] using hv⟩

end PolycyclicRecognition

end

end OAI
