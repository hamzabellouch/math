import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Length

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem length_filtration_step (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R B = Module.length R A + Module.length R (B ⧸ A.submoduleOf B) := by
  have h := Module.length_eq_add_of_exact (A.submoduleOf B).subtype
    (A.submoduleOf B).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(Submodule.submoduleOfEquivOfLe hAB).length_eq] at h
  exact h

theorem length_eq_sum_filtration
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (hzero : N 0 = ⊥) (n : ℕ) :
    Module.length R (N n) =
      ∑ i ∈ Finset.range n, Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have hlen := congrArg (fun A : Submodule R M => Module.length R A) hzero
    exact hlen.trans Module.length_eq_zero
  | succ n ih =>
    rw [length_filtration_step (N n) (N (n + 1)) (hmono n), ih,
      Finset.sum_range_succ]

theorem module_length_eq_sum_filtration
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (hzero : N 0 = ⊥) (n : ℕ) (htop : N n = ⊤) :
    Module.length R M =
      ∑ i ∈ Finset.range n, Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  have hlen := congrArg (fun A : Submodule R M => Module.length R A) htop
  have hlen' : Module.length R (N n) = Module.length R M :=
    hlen.trans Module.length_top
  exact hlen'.symm.trans (length_eq_sum_filtration N hmono hzero n)

end PiExponentJets.W22

end OAI
