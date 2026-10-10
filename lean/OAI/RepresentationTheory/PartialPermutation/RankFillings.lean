import Mathlib
import OAI.RepresentationTheory.PartialPermutation.StandardTableaux

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma exists_rankEnumeration (α ι : Type*) [Fintype α] [LinearOrder ι]
    (r : α → ι) :
    ∃ e : α ≃ Fin (Fintype.card α), ∀ a b, r a < r b → e a < e b := by
  classical
  let e₀ := Fintype.equivFin α
  let key : α → ι ×ₗ Fin (Fintype.card α) := fun a => toLex (r a, e₀ a)
  have hk : Function.Injective key := by
    intro a b h
    exact e₀.injective (congrArg (fun z : ι ×ₗ Fin (Fintype.card α) => (ofLex z).2) h)
  let : LinearOrder α := LinearOrder.lift' key hk
  let e := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨e.toEquiv, ?_⟩
  intro a b h
  apply e.strictMono
  exact Prod.Lex.left _ _ h

def fiberPermutation {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a = i}) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv r).symm.trans
    ((Equiv.sigmaCongrRight p).trans (Equiv.sigmaFiberEquiv r))

lemma fiberPermutation_apply {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a = i}) (a : α) :
    fiberPermutation r p a = (p (r a) ⟨a,rfl⟩).1 := rfl

lemma fiberPermutation_rank {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a = i}) (a : α) :
    r (fiberPermutation r p a) = r a := (p (r a) ⟨a,rfl⟩).2

lemma fiberPermutation_injective {α ι : Type*} (r : α → ι) :
    Function.Injective (fiberPermutation r) := by
  intro p q h
  funext i
  apply Equiv.ext
  rintro ⟨a,ha⟩
  subst i
  apply Subtype.ext
  exact Equiv.congr_fun h a

lemma rank_factorial_le_filling_count (α ι : Type*) [Fintype α] [PartialOrder α]
    [Fintype ι] [LinearOrder ι] (r : α → ι) (hr : StrictMono r) :
    (∏ i, (Fintype.card {a // r a = i}).factorial) ≤
      Fintype.card (StandardFilling α) := by
  classical
  obtain ⟨e,he⟩ := exists_rankEnumeration α ι r
  let f : (∀ i, Equiv.Perm {a // r a = i}) → StandardFilling α := fun p =>
    ⟨(fiberPermutation r p).trans e, fun a b hab => he _ _ (by
      simpa only [fiberPermutation_rank] using hr hab)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply fiberPermutation_injective r
    apply Equiv.ext
    intro a
    apply e.injective
    exact congrArg (fun t : StandardFilling α => t.1 a) hpq
  simpa only [Fintype.card_pi, Fintype.card_perm] using Fintype.card_le_of_injective f hf

lemma two_pow_pred_le_factorial (n : ℕ) : 2^(n-1) ≤ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · simp
    · rw [Nat.factorial_succ]
      simp only [Nat.add_sub_cancel] at ih ⊢
      calc
        2^(n+1) = 2 * 2^n := by rw [pow_succ]; omega
        _ ≤ (n+2) * (n+1).factorial := Nat.mul_le_mul (by omega) ih

lemma power_count_sub_ranks_le_factorials (ι : Type*) [Fintype ι] (a : ι → ℕ) :
    2^((∑ i, a i)-Fintype.card ι) ≤ ∏ i, (a i).factorial := by
  classical
  have h : ∑ i, a i ≤ (∑ i, (a i-1)) + Fintype.card ι := by
    calc
      _ ≤ ∑ i, (a i-1+1) := Finset.sum_le_sum (fun i _ => by omega)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  calc
    _ ≤ 2^(∑ i, (a i-1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ∏ i, 2^(a i-1) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := Finset.prod_le_prod (fun index _ => two_pow_pred_le_factorial (a index))

lemma rank_power_le_filling_count (α ι : Type*) [Fintype α] [PartialOrder α]
    [Fintype ι] [LinearOrder ι] (r : α → ι) (hr : StrictMono r) :
    2^(Fintype.card α - Fintype.card ι) ≤ Fintype.card (StandardFilling α) := by
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv r)
  rw [Fintype.card_sigma] at hh
  rw [← hh]
  exact (power_count_sub_ranks_le_factorials ι (fun i => Fintype.card {a // r a=i})).trans
    (rank_factorial_le_filling_count α ι r hr)

end
end Tableau
end PartialPermutation
end

end OAI
