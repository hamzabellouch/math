import OAI.Combinatorics.ContingencyTables.Transport.RationalProducts
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI

/-! # Independent finite coordinate maps and uniform product laws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

theorem mapLaw_id {A : Type*} [Fintype A] [DecidableEq A] (p : RationalLaw A) : mapLaw p id = p := by
  apply RationalLaw.ext
  funext y
  simp [mapLaw]

theorem mapLaw_comp {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (p : RationalLaw A) (f : A → B) (g : B → C) :
    mapLaw (mapLaw p f) g = mapLaw p (fun x => g (f x)) := by
  apply RationalLaw.ext
  funext z
  change (∑ y, if g y = z then ∑ x, if f x = y then p.mass x else 0 else 0) = _
  calc
    _ = ∑ y, ∑ x, if f x = y then (if g y = z then p.mass x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp [mapLaw]

theorem mapLaw_product {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] [DecidableEq (C × D)]
    (p : RationalLaw A) (q : RationalLaw B) (f : A → C) (g : B → D) :
    mapLaw (productLaw p q) (fun z => (f z.1, g z.2)) = productLaw (mapLaw p f) (mapLaw q g) := by
  apply RationalLaw.ext
  funext z
  change (∑ x : A × B, if (f x.1, g x.2) = z then p.mass x.1 * q.mass x.2 else 0) =
    (∑ x, if f x = z.1 then p.mass x else 0) * (∑ y, if g y = z.2 then q.mass y else 0)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = z.1 <;> by_cases hy : g y = z.2 <;> simp [Prod.ext_iff, hx, hy]

theorem mapLaw_equiv_output {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    (e : B ≃ C) (p : RationalLaw A) (f : A → B) :
    mapLaw p (fun x => e (f x)) = equivLaw e (mapLaw p f) := by
  apply RationalLaw.ext
  funext y
  change (∑ x, if e (f x) = y then p.mass x else 0) =
    ∑ x, if f x = e.symm y then p.mass x else 0
  simp only [← Equiv.eq_symm_apply]

variable {n : ℕ} {α β : Fin n → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]

theorem pi_mapLaw [∀ i, DecidableEq (β i)] [DecidableEq (∀ i, β i)] (p : ∀ i, RationalLaw (α i)) (f : ∀ i, α i → β i) :
    mapLaw (piLaw p) (fun x i => f i (x i)) = piLaw (fun i => mapLaw (p i) (f i)) := by
  apply RationalLaw.ext
  funext y
  change (∑ x : ∀ i, α i, if (fun i => f i (x i)) = y then ∏ i, (p i).mass (x i) else 0) =
    ∏ i, ∑ x : α i, if f i x = y i then (p i).mass x else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  congr 1
  exact propext funext_iff

omit [∀ i, Fintype (β i)] in
theorem pi_uniformLaw [∀ i, Nonempty (α i)] :
    piLaw (fun i => uniformLaw (α := α i)) = uniformLaw (α := ∀ i, α i) := by
  apply RationalLaw.ext
  funext x
  change (∏ i, (1 : ℚ) / Fintype.card (α i)) = 1 / Fintype.card (∀ i, α i)
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod, Fintype.card_pi]

end

end ContingencyTables.FirstSuccess

end OAI
