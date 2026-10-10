import OAI.Algebra.Finitistic.Encoding.QuadraticPresentation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

variable (R : Type*) [CommRing R] (α : Type*)

abbrev Term := Unit ⊕ (α ⊕ (α × α))

def term : Term α → FreeAlgebra R α
  | .inl _ => 1
  | .inr (.inl a) => FreeAlgebra.ι R a
  | .inr (.inr (a,b)) => FreeAlgebra.ι R a * FreeAlgebra.ι R b

/-- The degree bound is exactly the span of constants, generators, and ordered
products of two generators. The two factors are never commuted. -/
theorem degreeLE_two_eq_span :
    degreeLE R α 2 = Submodule.span R (Set.range (term R α)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨w,hw,rfl⟩
    apply Submodule.subset_span
    cases w with
    | nil => exact ⟨.inl (), rfl⟩
    | cons a w =>
      cases w with
      | nil => exact ⟨.inr (.inl a), by simp [term, word]⟩
      | cons b w =>
        cases w with
        | nil => exact ⟨.inr (.inr (a,b)), by simp [term, word]⟩
        | cons c w => simp only [List.length_cons] at hw; omega
  · apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    rcases i with u | (a | ⟨a,b⟩)
    · exact one_mem_degreeLE 2
    · exact generator_mem_degreeLE a
    · exact product_mem_degreeLE a b

/-- Finite coefficient form, suitable for the source's homogenization rule. -/
def coefficientPolynomial [Fintype α] (c : R) (l : α → R) (q : α → α → R) :
    FreeAlgebra R α :=
  algebraMap R (FreeAlgebra R α) c +
    ∑ a, l a • FreeAlgebra.ι R a +
    ∑ a, ∑ b, q a b • (FreeAlgebra.ι R a * FreeAlgebra.ι R b)

theorem exists_coefficients [Fintype α] (p : FreeAlgebra R α)
    (h : p ∈ degreeLE R α 2) :
    ∃ (c : R) (l : α → R) (q : α → α → R), coefficientPolynomial R α c l q = p := by
  rw [degreeLE_two_eq_span] at h
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h
  refine ⟨f (.inl ()), fun a => f (.inr (.inl a)),
    fun a b => f (.inr (.inr (a,b))), ?_⟩
  simpa [coefficientPolynomial, Fintype.sum_sum_type, Fintype.sum_prod_type,
    term, Algebra.smul_def, add_assoc] using hf

theorem coefficientPolynomial_degree [Fintype α] (c : R) (l : α → R) (q : α → α → R) :
    coefficientPolynomial R α c l q ∈ degreeLE R α 2 := by
  unfold coefficientPolynomial
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · simpa only [Algebra.smul_def, mul_one] using
        (degreeLE R α 2).smul_mem c (one_mem_degreeLE (R := R) (α := α) 2)
    · exact Submodule.sum_mem _ (fun a _ =>
        (degreeLE R α 2).smul_mem (l a) (generator_mem_degreeLE a))
  · exact Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ =>
      (degreeLE R α 2).smul_mem (q a b) (product_mem_degreeLE a b)))

/-- An exact characterization; the degree predicate hides no higher terms. -/
theorem degreeLE_two_iff_coefficients [Fintype α] (p : FreeAlgebra R α) :
    p ∈ degreeLE R α 2 ↔
      ∃ (c : R) (l : α → R) (q : α → α → R), coefficientPolynomial R α c l q = p := by
  refine ⟨exists_coefficients R α p, ?_⟩
  rintro ⟨c,l,q,rfl⟩
  exact coefficientPolynomial_degree R α c l q

/-- Every new quadratic relation has explicit constant, linear, and ordered
quadratic coefficients, with a simultaneous choice for the whole finite family. -/
theorem relation_coefficients [Finite α] {κ : Type*} (p : κ → FreeAlgebra R α) (N : ℕ) :
    letI := Fintype.ofFinite (Letter α N)
    ∃ (c : EquationIndex α N (κ := κ) → R)
      (l : EquationIndex α N (κ := κ) → Letter α N → R)
      (q : EquationIndex α N (κ := κ) → Letter α N → Letter α N → R),
      ∀ i, coefficientPolynomial R (Letter α N) (c i) (l i) (q i) = relation R α p N i := by
  let := Fintype.ofFinite (Letter α N)
  have h := fun i => exists_coefficients R (Letter α N) (relation R α p N i)
    (relation_degree R α p N i)
  choose c l q h using h
  exact ⟨c,l,q,h⟩

end LittleFinitistic.QuadraticPresentation

end

end OAI
