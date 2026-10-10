import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI


open scoped BigOperators

namespace InternalCatalan

theorem oddPrime_residue_sum_gather {R : Type*} [Semiring R]
    {p ell H : ℕ} (hp : 0 < p) (hell : ell < p)
    (a g : ℕ → R) (ha : ∀ i, H ≤ i → a i = 0) :
    (∑ i ∈ Finset.range H, if i % p = ell then a i * g (i / p) else 0) =
      ∑ u ∈ Finset.range H, a (u * p + ell) * g u := by
  classical
  have hmod (u : ℕ) : (u * p + ell) % p = ell := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hell]
  have hquot (u : ℕ) : (u * p + ell) / p = u := by
    rw [Nat.mul_comm u p, Nat.mul_add_div hp, Nat.div_eq_of_lt hell, add_zero]
  refine Finset.sum_bij_ne_zero (fun i _ _ => i / p) ?_ ?_ ?_ ?_
  · intro i hi hfi
    exact Finset.mem_range.mpr ((Nat.div_le_self i p).trans_lt (Finset.mem_range.mp hi))
  · intro i hi hfi j hj hfj heq
    have hir : i % p = ell := by
      by_contra h
      exact hfi (ite_eq_right h)
    have hjr : j % p = ell := by
      by_contra h
      exact hfj (ite_eq_right h)
    have hdi := Nat.mod_add_div i p
    have hdj := Nat.mod_add_div j p
    rw [hir, heq] at hdi
    rw [hjr] at hdj
    omega
  · intro u hu hgu
    have hlt : u * p + ell < H := by
      by_contra h
      have hz := ha (u * p + ell) (by omega)
      exact hgu (by rw [hz, zero_mul])
    refine ⟨u * p + ell, Finset.mem_range.mpr hlt, ?_, hquot u⟩
    simpa only [ite_eq_left (hmod u), hquot u] using hgu
  · intro i hi hfi
    have hir : i % p = ell := by
      by_contra h
      exact hfi (ite_eq_right h)
    have heq : i / p * p + ell = i := by
      have h := Nat.mod_add_div i p
      rw [hir] at h
      simpa only [Nat.add_comm, Nat.mul_comm] using h
    rw [ite_eq_left hir, heq]

end InternalCatalan

end OAI
