import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Fin
import OAI.Analysis.Laughlin.EnergyNonnegative

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem antisymmetric_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (a : Configuration N Q) :
    ψ (a ∘ σ) = σ.sign • ψ a := by
  induction σ using Equiv.Perm.swap_induction_on' generalizing a with
  | one => simp
  | mul_swap σ i j hij ih =>
    change ψ ((a ∘ σ) ∘ Equiv.swap i j) = _
    rw [hψ i j hij, ih]
    simp [map_mul, Equiv.Perm.sign_swap hij]

theorem antisymmetric_insertNth {n Q : ℕ} {ψ : State (n+1) Q}
    (hψ : Antisymmetric ψ) (k : Fin (n+1)) (i : Fin (Q+1)) (a : Configuration n Q) :
    ψ (k.insertNth i a) = (-1 : ℂ)^k.val * ψ (Fin.cons i a) := by
  rw [← Fin.cons_comp_cycleRange, antisymmetric_perm hψ]
  simp [Units.smul_def]

theorem antisymmetric_cons {n Q : ℕ} {ψ : State (n+1) Q}
    (hψ : Antisymmetric ψ) (i : Fin (Q+1)) :
    Antisymmetric (fun a : Configuration n Q => ψ (Fin.cons i a)) := by
  intro j k hjk a
  change ψ (Fin.cons i (a ∘ Equiv.swap j k)) = _
  rw [show Fin.cons i (a ∘ Equiv.swap j k) =
    Fin.cons i a ∘ Equiv.swap j.succ k.succ from Matrix.cons_swap i a j k]
  exact hψ j.succ k.succ (by simpa using hjk) (Fin.cons i a)

theorem sum_config_insert {n Q : ℕ} {M : Type*} [AddCommMonoid M]
    (k : Fin (n+1)) (f : Configuration (n+1) Q → M) :
    ∑ a, f a = ∑ i : Fin (Q+1), ∑ b : Configuration n Q, f (k.insertNth i b) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n+1) => Fin (Q+1)) k).sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_config_cons {n Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Configuration (n+1) Q → M) :
    ∑ a, f a = ∑ i : Fin (Q+1), ∑ b : Configuration n Q, f (Fin.cons i b) := by
  simpa using sum_config_insert (0 : Fin (n+1)) f

end Laughlin

end OAI
