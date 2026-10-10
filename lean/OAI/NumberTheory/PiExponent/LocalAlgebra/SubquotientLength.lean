import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Length

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def subquotientEquivImage (A B : Submodule R M) :
    (B ⧸ A.submoduleOf B) ≃ₗ[R] B.map A.mkQ := by
  let F : B →ₗ[R] M ⧸ A := A.mkQ.comp B.subtype
  have hker : LinearMap.ker F = A.submoduleOf B := by
    simp only [F, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.submoduleOf]
  have hrange : LinearMap.range F = B.map A.mkQ := by
    simp only [F, LinearMap.range_comp, Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

theorem quotient_length_step (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R (M ⧸ A) =
      Module.length R (B ⧸ A.submoduleOf B) + Module.length R (M ⧸ B) := by
  let T : Submodule R (M ⧸ A) := B.map A.mkQ
  have h := Module.length_eq_add_of_exact T.subtype T.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  change Module.length R (M ⧸ A) = Module.length R (B.map A.mkQ) +
    Module.length R ((M ⧸ A) ⧸ B.map A.mkQ) at h
  rw [← (subquotientEquivImage A B).length_eq,
    (Submodule.quotientQuotientEquivQuotient A B hAB).length_eq] at h
  exact h

theorem quotient_length_eq_sum_and_last
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1)) (n : ℕ) :
    Module.length R (M ⧸ N 0) =
      (∑ i ∈ Finset.range n,
        Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1)))) +
      Module.length R (M ⧸ N n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, quotient_length_step (N n) (N (n + 1)) (hmono n),
      Finset.sum_range_succ, add_assoc]

theorem quotient_length_eq_sum_of_last_top
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (n : ℕ) (htop : N n = ⊤) :
    Module.length R (M ⧸ N 0) =
      ∑ i ∈ Finset.range n,
        Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  have heq := congrArg (fun A : Submodule R M => Module.length R (M ⧸ A)) htop
  have hz : Module.length R (M ⧸ N n) = 0 := heq.trans Module.length_eq_zero
  simpa only [hz, add_zero] using quotient_length_eq_sum_and_last N hmono n

end PiExponentJets.W22

end OAI
