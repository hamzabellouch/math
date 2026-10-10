import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Module.Submodule.RestrictScalars

namespace OAI

/-!
# Multiplier orders and the saturation index

The initial arithmetic reduction in Section 2 of paper 031-01. A lattice
is represented by its actual integer submodule of a number field, not
by an abstract label. The two inclusions proved here are the algebraic
input to the discriminant bound `D(M) ≤ D(K) q^(2*n)`.
-/

open scoped NumberField

namespace DukePrimeDegree

variable {K : Type*} [Field K]

/-- Elements of the field preserving the given integer lattice. -/
def multiplierOrder (M : Submodule ℤ K) : Subalgebra ℤ K where
  carrier := {a | ∀ x ∈ M, a * x ∈ M}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by
    intro a b ha hb x hx
    simpa only [add_mul] using M.add_mem (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    simpa only [mul_assoc] using ha (b * x) (hb x hx)
  algebraMap_mem' := by
    intro a x hx
    simpa only [Algebra.smul_def] using M.smul_mem a hx

@[simp] theorem mem_multiplierOrder (M : Submodule ℤ K) (a : K) :
    a ∈ multiplierOrder M ↔ ∀ x ∈ M, a * x ∈ M := Iff.rfl

/-- A multiplier of a nonzero finitely generated lattice is integral.
This proves the upper inclusion in the manuscript's discriminant-scale
reduction directly from the library's determinant trick. -/
theorem multiplierOrder_le_integralClosure (M : Submodule ℤ K)
    (hne : M ≠ ⊥) (hfg : M.FG) :
    multiplierOrder M ≤ integralClosure ℤ K := by
  intro a ha
  exact isIntegral_of_smul_mem_submodule M hne hfg a ha

/-- The maximal-order span of an integer lattice. -/
def maximalOrderSpan (M : Submodule ℤ K) : Submodule (𝓞 K) K :=
  Submodule.span (𝓞 K) (M : Set K)

/-- The maximal-order span, viewed again as an integer lattice. -/
def saturationLattice (M : Submodule ℤ K) : Submodule ℤ K :=
  (maximalOrderSpan M).restrictScalars ℤ

lemma le_saturationLattice (M : Submodule ℤ K) : M ≤ saturationLattice M := by
  intro x hx
  exact Submodule.subset_span hx

/-- The original lattice inside its maximal-order span. -/
def latticeInSaturation (M : Submodule ℤ K) : Submodule ℤ (saturationLattice M) :=
  M.comap (saturationLattice M).subtype

/-- The additive index `[O_K M : M]`. For a full lattice this is finite.
As usual, the index is zero if the quotient is infinite. -/
noncomputable def saturationIndex (M : Submodule ℤ K) : ℕ :=
  (latticeInSaturation M).toAddSubgroup.index

/-- Multiplication by the index sends the saturation into the lattice. -/
lemma saturationIndex_nsmul_mem (M : Submodule ℤ K) {x : K}
    (hx : x ∈ saturationLattice M) : saturationIndex M • x ∈ M := by
  exact (latticeInSaturation M).toAddSubgroup.nsmul_index_mem
    (⟨x, hx⟩ : saturationLattice M)

/-- The conductor inclusion `q O_K ⊆ O(M)` with `q = [O_K M : M]`.
Together with integrality of multipliers, this gives the two order
inclusions used in the manuscript. -/
theorem saturationIndex_mul_integer_mem_multiplierOrder
    (M : Submodule ℤ K) (r : 𝓞 K) :
    (saturationIndex M : K) * (r : K) ∈ multiplierOrder M := by
  intro x hx
  have hspan : (r : K) * x ∈ saturationLattice M := by
    exact (maximalOrderSpan M).smul_mem r (Submodule.subset_span hx)
  simpa only [nsmul_eq_mul, mul_assoc] using saturationIndex_nsmul_mem M hspan

end DukePrimeDegree

end OAI
