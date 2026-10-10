import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicKernelRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianRankDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicQuotientDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedCountable
import Mathlib.LinearAlgebra.Dimension.Localization

namespace OAI

/-! # Integral dimension for torsion-free abelian-by-infinite-cyclic groups of type FP∞

The rational rank bound is obtained from the actual second homology of the
kernel, then used in the countable-union dimension argument.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative TensorProduct
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsCyclic (G ⧸ N)]

theorem abelian_cyclic_kernel_finite_rank (h : TypeFPInfinity G) :
    ∃ d : ℕ, Module.rank ℤ (Additive N) ≤ d := by
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  let f := zpowersHom (G ⧸ N) z
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨i, hi⟩ := hz q
    exact ⟨Multiplicative.ofAdd i, hi⟩
  let := abelian_cyclic_kernel_finite_rational_rank N h f hf
  refine ⟨Module.finrank ℚ (ℚ ⊗[ℤ] Additive N), ?_⟩
  rw [← (TensorProduct.isBaseChange (R := ℤ) (S := ℚ) (M := Additive N)).rank_eq,
    ← Module.finrank_eq_rank]

theorem abelian_infiniteCyclic_finite_dimension [Infinite (G ⧸ N)]
    (h : TypeFPInfinity G) (htf : HasNoNontrivialTorsion N) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨d, hd⟩ := abelian_cyclic_kernel_finite_rank N h
  let : Countable G := countable_of_group_fg G
  let : Countable N := inferInstance
  let := abelian_cohomologicalDimension_of_rank d hd htf
  exact ⟨d + 1 + 1, cohomologicalDimension_le_of_infiniteCyclicQuotient N (d + 1)⟩

end PolycyclicRecognition

end

end OAI
