import OAI.NumberTheory.Ostmann.Characters.SparseCoefficientMajorant
import OAI.NumberTheory.Ostmann.Characters.SparseProductCharacter
import OAI.NumberTheory.Ostmann.Characters.SparseConductorCutoff

namespace OAI

/-! # Nonzero coefficients have the manuscript's short conductor support -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparseTruncatedMellinCoefficient_support_card {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i)))
    (t : ℝ) (K : ℕ) (χ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hc : sparseTruncatedMellinCoefficient p E t K χ ≠ 0) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => χ i ≠ 1)).card ≤ 2 * K := by
  unfold sparseTruncatedMellinCoefficient at hc
  obtain ⟨v, hv, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have hvK := (Finset.mem_filter.mp hv).2
  have hn (i : Fin n) := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ _)
  have hb (i : Fin n) : χ i ≠ 1 → (v i).1 = true ∨ (v i).2 = true := by
    intro hχ
    by_contra h
    have h₁ : (v i).1 = false := by cases hh : (v i).1 <;> simp_all
    have h₂ : (v i).2 = false := by cases hh : (v i).2 <;> simp_all
    have he : v i = (false, false) := Prod.ext h₁ h₂
    have hh := hn i
    simp only [he, sparsePatternMellin, hχ, ite_false, ne_eq, not_true_eq_false] at hh
  have hsum : ((Finset.univ : Finset (Fin n)).filter (fun i => χ i ≠ 1)).card ≤
      cubeDegree v false + cubeDegree v true := by
    rw [Finset.card_filter]
    unfold cubeDegree
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hχ : χ i = 1
    · simp [hχ]
    · have hh := hb i hχ
      rcases hh with hh | hh <;> simp [hχ, hh]
  omega

theorem sparse_coefficient_primitive_modulus_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (C L t : ℝ)
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hc : sparseTruncatedMellinCoefficient p E t (sparseTruncationDegree C L) χ ≠ 0)
    (hlog : ∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L))
    (ρ : PrimitiveComplexCharacter)
    (hρ : primitiveCharacterReduction (sparseProductCharacter p χ) = some ρ) :
    ρ.modulus ≤ sparseConductorCutoff C L := by
  let S := (Finset.univ : Finset (Fin n)).filter (fun i => χ i ≠ 1)
  have hthrough := sparseProductCharacter_factorsThrough p χ S (by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  apply (primitiveCharacterReduction_modulus_le _ hthrough ρ hρ).trans
  apply sparse_product_le_conductor_cutoff S p C L
  · intro i _
    exact (Fact.out : (p i).Prime).pos
  · intro i _
    exact hlog i
  · exact sparseTruncatedMellinCoefficient_support_card p E t _ χ hc

end Ostmann

end OAI
