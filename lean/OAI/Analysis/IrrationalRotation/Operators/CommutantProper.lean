import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

namespace OAI

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem centralizer_singleton_eq_top_iff_scalar (T : H →L[ℂ] H) :
    Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) = ⊤ ↔
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  rw [Subalgebra.centralizer_eq_top_iff_subset]
  simp only [Set.singleton_subset_iff, Algebra.IsCentral.center_eq_bot]
  simp [Algebra.algebraMap_eq_smul_one, eq_comm]

theorem centralizer_singleton_ne_top_of_nonscalar (T : H →L[ℂ] H)
    (hT : ¬ ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) :
    Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) ≠ ⊤ := by
  exact fun h => hT ((centralizer_singleton_eq_top_iff_scalar T).mp h)

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem centralizer_singleton_add_scalar (T : A) (c : ℂ) :
    Subalgebra.centralizer ℂ ({T + c • (1 : A)} : Set A) =
      Subalgebra.centralizer ℂ ({T} : Set A) := by
  ext S
  simp only [Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, add_right_cancel_iff]

theorem centralizer_singleton_one_add (T : A) :
    Subalgebra.centralizer ℂ ({1 + T} : Set A) =
      Subalgebra.centralizer ℂ ({T} : Set A) := by
  simpa only [one_smul, add_comm] using centralizer_singleton_add_scalar T 1

end Invariant233

end OAI
