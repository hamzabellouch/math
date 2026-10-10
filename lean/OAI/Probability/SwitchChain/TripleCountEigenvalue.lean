import OAI.Probability.SwitchChain.TripleCountLaw
import OAI.Probability.SwitchChain.CountEigenEquation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def marginal (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) (t : Fin (m + 1)) : ℝ :=
  ∑ x : Triple m, if x.val i = t then probability a x else 0

theorem marginal_sum (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) :
    ∑ t : Fin (m + 1), marginal a m i t = 1 := by
  classical
  unfold marginal
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact probability_sum a m

theorem marginal_positive (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3)
    (t : Fin (m + 1)) : 0 < marginal a m i t := by
  have h := marginal_pos a m (Equiv.swap 0 i) t.val (by have := t.isLt; omega)
  simpa only [marginal, Equiv.swap_apply_left, Fin.val_eq_val] using h

theorem conditional_eigenvalue_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (lam : ℝ)
    (hcenter : ∀ i, ∑ t : Fin (m + 1), marginal a m i t * b i t.val = 0)
    (hne : ∃ i, ∃ t : Fin (m + 1), b i t.val ≠ 0)
    (heig : ∀ i t, t ≤ m → lam * b i t =
      conditionalAverage a (rowSum b : Triple m → ℝ) (Equiv.swap 0 i) t) :
    lam ≤ 2 := by
  apply CountEigenvalue.count_eigenvalue_le_two_of_centered m a
    (fun i => Equiv.swap 0 i 1) (fun i => Equiv.swap 0 i 2) b
    (marginal a m) lam (marginal_sum a m) hcenter hne
  intro i t ht
  have h := heig i t ht
  rw [conditionalAverage_rowSum a m b (Equiv.swap 0 i) t ht,
    Equiv.swap_apply_left] at h
  nlinarith

end Problem315.TripleCountLaw

end

end OAI
