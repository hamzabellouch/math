import OAI.Algebra.DepthFive.Pairings
import OAI.Algebra.DepthFive.LocalMomentPolynomials

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

/-- A valid source-occupation shift arising from two paths at a single layer. -/
def ShiftRelation {σ : Type*} (derivative : Bool) (M M' : σ → ℕ) (p q : σ) : Prop :=
  ∀ x, (M' x : ℤ) = (M x : ℤ) + (if derivative then -1 else 1) *
    ((Finsupp.single p (1 : ℤ) - Finsupp.single q 1 : σ →₀ ℤ) x)

lemma shiftRelation_normal {σ : Type*} (derivative : Bool) (M M' : σ → ℕ) (p : σ)
    (h : ShiftRelation derivative M M' p p) : M' = M := by
  funext x
  have hx := h x
  simp only [sub_self, Finsupp.zero_apply, mul_zero, add_zero] at hx
  exact_mod_cast hx

lemma shiftRelation_derivative {σ : Type*} (M M' : σ → ℕ) (p q : σ) (hpq : p ≠ q)
    (h : ShiftRelation true M M' p q) : M' q = M q + 1 := by
  classical
  have hq := h q
  simp [Finsupp.sub_apply, Ne.symm hpq] at hq
  omega

lemma shiftRelation_multiplication {σ : Type*} (M M' : σ → ℕ) (p q : σ) (hpq : p ≠ q)
    (h : ShiftRelation false M M' p q) : M' q + 1 = M q := by
  classical
  have hq := h q
  simp [Finsupp.sub_apply, Ne.symm hpq] at hq
  omega

/-- The complete local second-trace polynomial. The all-equal case belongs to normal pairing. -/
def localPolynomial {σ : Type*} [DecidableEq σ] (derivative : Bool)
    (M : σ → ℕ) (p q r : σ) : ℝ :=
  if p = q then mass derivative (M p) * mass derivative (M r)
  else if derivative then (M p : ℝ) * ((M q : ℝ) + 1)
  else ((M p : ℝ) + 1) * (M q : ℝ)

/-- Matching signed coordinate differences and the actual source shift imply precisely
    the normal/diagonal local polynomial table from the four-path expansion. -/
theorem fourCoefficient_eq_localPolynomial {σ : Type*} [DecidableEq σ]
    (derivative : Bool) (M M' : σ → ℕ) (p q r s : σ)
    (hmatch : Finsupp.single p (1 : ℤ) - Finsupp.single q 1 =
      Finsupp.single r 1 - Finsupp.single s 1)
    (hshift : ShiftRelation derivative M M' p q) :
    fourCoefficient derivative (M p) (M' q) (M r) (M' s) =
      localPolynomial derivative M p q r := by
  rcases (Pairings.coordinate_difference_eq_iff_exclusive p q r s).mp hmatch with hN | hD
  · rcases hN with ⟨hpq, hrs⟩
    subst q
    subst s
    have hM := shiftRelation_normal derivative M M' p hshift
    subst M'
    simp [localPolynomial, normal_fourCoefficient]
  · rcases hD with ⟨hpr, hqs, hpq⟩
    subst r
    subst s
    cases derivative
    · have hq := shiftRelation_multiplication M M' p q hpq hshift
      simpa [localPolynomial, hpq] using
        multiplication_diagonal_layer M M' p q hq
    · have hq := shiftRelation_derivative M M' p q hpq hshift
      simpa [localPolynomial, hpq] using derivative_diagonal_layer M M' p q hq

lemma localPolynomial_nonneg {σ : Type*} [DecidableEq σ] (derivative : Bool)
    (M : σ → ℕ) (p q r : σ) : 0 ≤ localPolynomial derivative M p q r := by
  unfold localPolynomial
  split_ifs
  · exact mul_nonneg (mass_nonneg _ _) (mass_nonneg _ _)
  all_goals positivity

/-- The local table applies simultaneously at all layers, converting the four path
coefficient products into a product of occupation polynomials. -/
theorem four_path_products_eq_localPolynomial_product {ι σ : Type*} [DecidableEq σ]
    (layers : Finset ι) (derivative : ι → Bool) (M M' : ι → σ → ℕ)
    (p q r s : ι → σ)
    (hmatch : ∀ t ∈ layers,
      Finsupp.single (p t) (1 : ℤ) - Finsupp.single (q t) 1 =
        Finsupp.single (r t) 1 - Finsupp.single (s t) 1)
    (hshift : ∀ t ∈ layers, ShiftRelation (derivative t) (M t) (M' t) (p t) (q t)) :
    (∏ t ∈ layers, coefficient (derivative t) (M t (p t))) *
      (∏ t ∈ layers, coefficient (derivative t) (M' t (q t))) *
      (∏ t ∈ layers, coefficient (derivative t) (M t (r t))) *
      (∏ t ∈ layers, coefficient (derivative t) (M' t (s t))) =
      ∏ t ∈ layers, localPolynomial (derivative t) (M t) (p t) (q t) (r t) := by
  rw [four_products_eq_product]
  apply Finset.prod_congr rfl
  intro t ht
  exact fourCoefficient_eq_localPolynomial (derivative t) (M t) (M' t)
    (p t) (q t) (r t) (s t) (hmatch t ht) (hshift t ht)

end LocalMoments
end Problem335

end

end OAI
