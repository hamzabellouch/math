import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # Expanding a finite ordered product of finite sums -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem ordered_product_sums {A J : Type*} [Semiring A] [Fintype J]
    {n : ℕ} (a : Fin n → J → A) :
    (List.ofFn (fun i => ∑ j, a i j)).prod =
      ∑ k : Fin n → J, (List.ofFn (fun i => a i (k i))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    symm
    calc
      _ = ∑ p : J × (Fin n → J),
          (List.ofFn (fun i => a i ((Fin.consEquiv (fun _ : Fin (n + 1) => J)) p i))).prod :=
        (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => J))
          (fun k => (List.ofFn (fun i => a i (k i))).prod)).symm
      _ = _ := by simp [Fintype.sum_prod_type, List.ofFn_succ]

end PolycyclicRecognition

end

end OAI
