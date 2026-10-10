import OAI.Combinatorics.ContingencyTables.Transport.FirstSuccess
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace OAI

/-! # Finite product laws for the independent bounded offset draws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

def piLaw {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (p : ∀ i, RationalLaw (α i)) : RationalLaw (∀ i, α i) where
  mass := fun x => ∏ i, (p i).mass (x i)
  nonnegative := fun x => Finset.prod_nonneg (fun i _ => (p i).nonnegative (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [(p _).total, Finset.prod_const_one]

theorem variation_pi_succ {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, Fintype (α i)]
    (p q : ∀ i, RationalLaw (α i)) :
    variation (piLaw p) (piLaw q) =
      variation (productLaw (p 0) (piLaw (fun i : Fin n => p i.succ)))
        (productLaw (q 0) (piLaw (fun i : Fin n => q i.succ))) := by
  unfold variation
  congr 1
  apply Fintype.sum_equiv (Fin.consEquiv α).symm
  intro x
  change |(∏ i, (p i).mass (x i)) - (∏ i, (q i).mass (x i))| =
    |(p 0).mass (x 0) * (∏ i : Fin n, (p i.succ).mass (x i.succ)) -
      (q 0).mass (x 0) * (∏ i : Fin n, (q i.succ).mass (x i.succ))|
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]

/-- Errors in independent coordinate draws add before any success test
or deterministic table completion is applied. -/
theorem variation_pi {n : ℕ} (α : Fin n → Type*) [∀ i, Fintype (α i)]
    (p q : ∀ i, RationalLaw (α i)) :
    variation (piLaw p) (piLaw q) ≤ ∑ i, variation (p i) (q i) := by
  induction n with
  | zero => simp [variation, piLaw]
  | succ n ih =>
    have hi := ih (fun i : Fin n => α i.succ)
      (fun i : Fin n => p i.succ) (fun i : Fin n => q i.succ)
    calc
      _ = _ := variation_pi_succ α p q
      _ ≤ variation (p 0) (q 0) +
          variation (piLaw (fun i : Fin n => p i.succ)) (piLaw (fun i : Fin n => q i.succ)) :=
        variation_product _ _ _ _
      _ ≤ variation (p 0) (q 0) + ∑ i : Fin n, variation (p i.succ) (q i.succ) :=
        add_le_add le_rfl hi
      _ = _ := (Fin.sum_univ_succ (fun i => variation (p i) (q i))).symm

end ContingencyTables.FirstSuccess

end OAI
