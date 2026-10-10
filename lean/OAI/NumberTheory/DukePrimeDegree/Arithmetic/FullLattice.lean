import OAI.NumberTheory.DukePrimeDegree.Arithmetic.MultiplierOrder
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Basic

namespace OAI

/-!
# Full lattices in number fields

A full lattice is a finitely generated integer submodule spanning the
number field over the rationals. In a characteristic-zero field it is
free; the span condition forces its rank to be the field degree.
-/

namespace DukePrimeDegree

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The lattice data appearing in Theorem 1.1, before choosing an ordering
of the real embeddings. -/
structure FullLattice where
  toSubmodule : Submodule ℤ K
  fg : toSubmodule.FG
  span_eq_top : Submodule.span ℚ (toSubmodule : Set K) = ⊤

variable {K}

lemma FullLattice.ne_bot (M : FullLattice K) : M.toSubmodule ≠ ⊥ := by
  intro h
  have hs := M.span_eq_top
  rw [h] at hs
  change Submodule.span ℚ {0} = ⊤ at hs
  rw [Submodule.span_zero_singleton] at hs
  exact bot_ne_top hs

/-- The multiplier order of a full lattice consists of algebraic integers. -/
lemma FullLattice.multiplierOrder_le (M : FullLattice K) :
    multiplierOrder M.toSubmodule ≤ integralClosure ℤ K :=
  multiplierOrder_le_integralClosure M.toSubmodule M.ne_bot M.fg

/-- Every field element has an integer denominator relative to a full
lattice. This is a direct application of localization of spans. -/
lemma FullLattice.exists_integer_multiple (M : FullLattice K) (x : K) :
    ∃ q : ℤ, q ≠ 0 ∧ q • x ∈ M.toSubmodule := by
  have hx : x ∈ Submodule.span ℚ (M.toSubmodule : Set K) := by
    rw [M.span_eq_top]
    trivial
  obtain ⟨q, hq⟩ := multiple_mem_span_of_mem_localization_span
    (R' := ℚ) (nonZeroDivisors ℤ) (M.toSubmodule : Set K) x hx
  refine ⟨q, mem_nonZeroDivisors_iff_ne_zero.mp q.property, ?_⟩
  simpa only [Submodule.span_eq, Submonoid.smul_def] using hq

/-- The maximal-order saturation is again finitely generated over the integers. -/
lemma FullLattice.saturation_fg (M : FullLattice K) :
    (saturationLattice M.toSubmodule).FG := by
  exact (M.fg.span (A := 𝓞 K)).restrictScalars

/-- A full lattice has finite, nonzero index in its maximal-order saturation. -/
lemma FullLattice.saturationIndex_pos (M : FullLattice K) :
    0 < saturationIndex M.toSubmodule := by
  let S := saturationLattice M.toSubmodule
  let N := latticeInSaturation M.toSubmodule
  let : Module.Finite ℤ S := Module.Finite.iff_fg.mpr M.saturation_fg
  have htorsion : Module.IsTorsion ℤ (S ⧸ N) := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
    obtain ⟨q, hq, hx⟩ := M.exists_integer_multiple (x : K)
    refine ⟨⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hx
  let : Finite (S ⧸ N) := Module.finite_of_fg_torsion _ htorsion
  change 0 < Nat.card (S ⧸ N)
  exact Nat.card_pos

end DukePrimeDegree

end OAI
