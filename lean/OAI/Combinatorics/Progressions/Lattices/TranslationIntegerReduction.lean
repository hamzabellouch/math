import Mathlib.Algebra.Order.Floor.Ring
import OAI.Combinatorics.Progressions.Geometry.TopSupportSubstitution
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {B : Type*}

noncomputable def integerFloorPolynomial (P : MvPolynomial B ℝ) : MvPolynomial B ℤ :=
  ∑ α ∈ P.support, monomial α ⌊P.coeff α⌋

@[simp] theorem coeff_integerFloorPolynomial (P : MvPolynomial B ℝ) (α : B →₀ ℕ) :
    (integerFloorPolynomial P).coeff α = ⌊P.coeff α⌋ := by
  classical
  by_cases hα : α ∈ P.support
  · simp [integerFloorPolynomial, coeff_monomial, hα]
  · have hzero : P.coeff α = 0 := by
      by_contra hn
      exact hα (mem_support_iff.mpr hn)
    simp [integerFloorPolynomial, coeff_monomial, hα, hzero]

theorem integerFloorPolynomial_support_subset (P : MvPolynomial B ℝ) :
    (integerFloorPolynomial P).support ⊆ P.support := by
  intro α hα
  rw [mem_support_iff, coeff_integerFloorPolynomial] at hα
  apply mem_support_iff.mpr
  intro hz
  exact hα (by rw [hz, Int.floor_zero])

theorem integerFloorPolynomial_mem_weightedSupportLT (w : B → ℕ) (d : ℕ)
    {P : MvPolynomial B ℝ} (hP : P ∈ weightedSupportLT w d) :
    integerFloorPolynomial P ∈ weightedSupportLT w d :=
  fun _ hα => hP (integerFloorPolynomial_support_subset P hα)

theorem polynomialTranslate_mem_weightedSupportLT {R : Type*} [CommRing R]
    (h : B → R) (w : B → ℕ) (d : ℕ)
    {P : MvPolynomial B R} (hP : P ∈ weightedSupportLT w d) :
    polynomialTranslate h P ∈ weightedSupportLT w d := by
  exact weightedSupportLT_aeval w w (fun i => X i + C (h i))
    (fun i => (weightedSupportLE w (w i)).add_mem
      (weightedSupportLE_X w i) (weightedSupportLE_C w (w i) (h i))) hP

namespace PolynomialTranslationGroupOver

noncomputable def integerReduction (g : PolynomialTranslationGroupOver ℝ B) :
    PolynomialTranslationGroupOver ℤ B where
  base i := -⌊g.base i⌋
  polynomial := -integerFloorPolynomial
    (polynomialTranslate (fun i => (⌊g.base i⌋ : ℝ)) g.polynomial)

@[simp] theorem integerReduction_base (g : PolynomialTranslationGroupOver ℝ B) (i : B) :
    (integerReduction g).base i = -⌊g.base i⌋ := rfl

theorem integerReduction_product_base (g : PolynomialTranslationGroupOver ℝ B) (i : B) :
    (g * map (Int.castRingHom ℝ) (integerReduction g)).base i = Int.fract (g.base i) := by
  change g.base i + ((-⌊g.base i⌋ : ℤ) : ℝ) = _
  rw [Int.cast_neg]
  rfl

theorem integerReduction_product_polynomial (g : PolynomialTranslationGroupOver ℝ B) :
    (g * map (Int.castRingHom ℝ) (integerReduction g)).polynomial =
      let P := polynomialTranslate (fun i => (⌊g.base i⌋ : ℝ)) g.polynomial
      P - MvPolynomial.map (Int.castRingHom ℝ) (integerFloorPolynomial P) := by
  simp only [polynomial_mul, map_polynomial, integerReduction, map_neg, sub_eq_add_neg]
  congr 1
  change polynomialTranslate (fun i => -((-⌊g.base i⌋ : ℤ) : ℝ)) g.polynomial = _
  simp only [Int.cast_neg, neg_neg]

theorem integerReduction_product_coefficient
    (g : PolynomialTranslationGroupOver ℝ B) (α : B →₀ ℕ) :
    (g * map (Int.castRingHom ℝ) (integerReduction g)).polynomial.coeff α =
      Int.fract ((polynomialTranslate (fun i => (⌊g.base i⌋ : ℝ)) g.polynomial).coeff α) := by
  rw [integerReduction_product_polynomial]
  simp only [coeff_sub, coeff_map, coeff_integerFloorPolynomial]
  rfl

theorem integerReduction_product_bounds (g : PolynomialTranslationGroupOver ℝ B) :
    (∀ i, 0 ≤ (g * map (Int.castRingHom ℝ) (integerReduction g)).base i ∧
      (g * map (Int.castRingHom ℝ) (integerReduction g)).base i < 1) ∧
    ∀ α, 0 ≤ (g * map (Int.castRingHom ℝ) (integerReduction g)).polynomial.coeff α ∧
      (g * map (Int.castRingHom ℝ) (integerReduction g)).polynomial.coeff α < 1 := by
  constructor
  · intro i
    rw [integerReduction_product_base]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · intro α
    rw [integerReduction_product_coefficient]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem integerReduction_weightedSupportLT (g : PolynomialTranslationGroupOver ℝ B)
    (w : B → ℕ) (d : ℕ) (hg : g.polynomial ∈ weightedSupportLT w d) :
    (integerReduction g).polynomial ∈ weightedSupportLT w d ∧
    (g * map (Int.castRingHom ℝ) (integerReduction g)).polynomial ∈ weightedSupportLT w d := by
  let P := polynomialTranslate (fun i => (⌊g.base i⌋ : ℝ)) g.polynomial
  have hP : P ∈ weightedSupportLT w d := polynomialTranslate_mem_weightedSupportLT _ w d hg
  have hfloor := integerFloorPolynomial_mem_weightedSupportLT w d hP
  refine ⟨(weightedSupportLT w d).neg_mem hfloor, ?_⟩
  rw [integerReduction_product_polynomial]
  apply (weightedSupportLT w d).sub_mem hP
  intro α hα
  exact hfloor (MvPolynomial.support_map_subset (Int.castRingHom ℝ) _ hα)

theorem exists_integer_reduction (g : PolynomialTranslationGroupOver ℝ B)
    (w : B → ℕ) (d : ℕ) (hg : g.polynomial ∈ weightedSupportLT w d) :
    ∃ γ : PolynomialTranslationGroupOver ℤ B,
      (∀ i, 0 ≤ (g * map (Int.castRingHom ℝ) γ).base i ∧
        (g * map (Int.castRingHom ℝ) γ).base i < 1) ∧
      (∀ α, 0 ≤ (g * map (Int.castRingHom ℝ) γ).polynomial.coeff α ∧
        (g * map (Int.castRingHom ℝ) γ).polynomial.coeff α < 1) ∧
      γ.polynomial ∈ weightedSupportLT w d ∧
      (g * map (Int.castRingHom ℝ) γ).polynomial ∈ weightedSupportLT w d :=
  ⟨integerReduction g, (integerReduction_product_bounds g).1,
    (integerReduction_product_bounds g).2, integerReduction_weightedSupportLT g w d hg⟩

end PolynomialTranslationGroupOver

end Erdos3

end

end OAI
