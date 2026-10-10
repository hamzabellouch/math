import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Ring

namespace OAI

section

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators Matrix

noncomputable section

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

/-- The `|n| * |ι|` alignment columns for a fixed parametrization and input set.
The input set is represented by any map `point : E → V`; no injectivity is
needed for the exact algebraic equivalence. -/
def alignmentMatrix (b : Basis ι R V) (point : E → V) (z : V → n → F) :
    Matrix E (n × ι) F :=
  fun e ij => algebraMap R F (b.repr (point e) ij.2) * z (point e) ij.1

/-- Basis values of a linear lift give the coefficients of the alignment
column combination.  The identity holds for every lift, without selecting
one in advance of the parametrization. -/
theorem dot_lift_eq_alignment_mulVec (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (g : V →ₗ[R] (n → F)) (e : E) :
    (∑ i, z (point e) i * g (point e) i) =
      (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e := by
  have hg : g (point e) = ∑ j, b.repr (point e) j • g (b j) := by
    calc
      g (point e) = g (∑ j, b.repr (point e) j • b j) :=
        congrArg g (b.sum_repr (point e)).symm
      _ = ∑ j, b.repr (point e) j • g (b j) := by simp only [map_sum, map_smul]
  rw [hg]
  simp only [Matrix.mulVec, dotProduct, alignmentMatrix,
    Finset.sum_apply, Algebra.smul_def, Pi.mul_apply,
    Pi.algebraMap_apply, Finset.mul_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Existence of *any* linear lift aligning on the chosen inputs is one
column-membership event.  In particular there is no field-size-dependent
union bound over the possible lifts. -/
theorem exists_lift_alignment_iff_mem_range (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (c : E → F) :
    (∃ g : V →ₗ[R] (n → F), ∀ e,
      (∑ i, z (point e) i * g (point e) i) = c e) ↔
      c ∈ LinearMap.range (alignmentMatrix b point z).mulVecLin := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun ij => g (b ij.2) ij.1, ?_⟩
    ext e
    change (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e = c e
    rw [← dot_lift_eq_alignment_mulVec]
    exact hg e
  · rintro ⟨u, hu⟩
    let g : V →ₗ[R] (n → F) := b.constr R (fun j i => u (i, j))
    refine ⟨g, ?_⟩
    intro e
    rw [dot_lift_eq_alignment_mulVec b point z g e]
    have hg : (fun ij : n × ι => g (b ij.2) ij.1) = u := by
      funext ij
      exact congrFun (b.constr_basis R (fun j i => u (i, j)) ij.2) ij.1
    rw [hg]
    exact congrFun hu e

/-- The column-space dimension is at most the number of free basis values.
For three field coordinates and a binary basis of size `r`, this is `3r`. -/
theorem finrank_alignment_range_le (b : Basis ι R V)
    (point : E → V) (z : V → n → F) [Fintype E] :
    Module.finrank F (LinearMap.range (alignmentMatrix b point z).mulVecLin) ≤
      Fintype.card n * Fintype.card ι := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using
      (LinearMap.finrank_range_le (alignmentMatrix b point z).mulVecLin)

end

end UniqueGamesTheorem.Quadratic

end

end OAI
