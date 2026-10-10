import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.PivotSummation
open Finset Classical
variable {σ P : Type*} {n : ℕ}

abbrev Unselected (sel : Fin n → σ) := {s : σ // s ∉ Set.range sel}

def splitSlots (sel : Fin n → σ) (hinj : Function.Injective sel) :
    (σ → P) ≃ (Fin n → P) × (Unselected sel → P) :=
  (Equiv.piEquivPiSubtypeProd (fun s => s ∈ Set.range sel) (fun _ => P)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective sel hinj).symm (Equiv.refl P)) (Equiv.refl _))

lemma splitSlots_first (sel : Fin n → σ) (hinj : Function.Injective sel) (x : σ → P) (i : Fin n) :
    (splitSlots sel hinj x).1 i = x (sel i) := rfl

lemma splitSlots_second (sel : Fin n → σ) (hinj : Function.Injective sel) (x : σ → P) (s : Unselected sel) :
    (splitSlots sel hinj x).2 s = x s.val := rfl

def mergeSlots (sel : Fin n → σ) (hinj : Function.Injective sel)
    (y : Fin n → P) (z : Unselected sel → P) : σ → P := (splitSlots sel hinj).symm (y,z)

lemma mergeSlots_selected (sel : Fin n → σ) (hinj : Function.Injective sel)
    (y : Fin n → P) (z : Unselected sel → P) (i : Fin n) :
    mergeSlots sel hinj y z (sel i)=y i := by
  have he := congrArg (fun x : (Fin n → P) × (Unselected sel → P) => x.1 i)
    ((splitSlots sel hinj).apply_symm_apply (y,z))
  exact he

lemma mergeSlots_unselected (sel : Fin n → σ) (hinj : Function.Injective sel)
    (y : Fin n → P) (z : Unselected sel → P) (s : Unselected sel) :
    mergeSlots sel hinj y z s.val=z s := by
  have he := congrArg (fun x : (Fin n → P) × (Unselected sel → P) => x.2 s)
    ((splitSlots sel hinj).apply_symm_apply (y,z))
  exact he

variable [Fintype σ] [Fintype P]

lemma prod_slots (sel : Fin n → σ) (hinj : Function.Injective sel) (f : σ → ℝ) :
    (∏ s, f s) = (∏ i, f (sel i)) * ∏ s : Unselected sel, f s.val := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun s => s ∈ Set.range sel) f]
  congr 1
  convert (Equiv.prod_comp (Equiv.ofInjective sel hinj) (fun s => f s.val)).symm using 1
  · congr 1
    ext x
    simp
  · rfl

lemma sum_slots (sel : Fin n → σ) (hinj : Function.Injective sel) (F : (σ → P) → ℝ) :
    (∑ x, F x) = ∑ z : Unselected sel → P, ∑ y : Fin n → P, F (mergeSlots sel hinj y z) := by
  rw [← Equiv.sum_comp (splitSlots sel hinj).symm F,Fintype.sum_prod_type,sum_comm]
  rfl

theorem slots_weighted_bound (sel : Fin n → σ) (hinj : Function.Injective sel)
    (W : σ → P → ℝ) (hW : ∀ s p, 0 ≤ W s p) (A : (σ → P) → ℝ)
    (K : ℝ) (hinner : ∀ z : Unselected sel → P,
      (∑ y : Fin n → P, A (mergeSlots sel hinj y z) * ∏ i, W (sel i) (y i)) ≤ K) :
    (∑ x : σ → P, A x * ∏ s, W s (x s)) ≤
      K * ∏ s : Unselected sel, ∑ p : P, W s.val p := by
  rw [sum_slots sel hinj]
  have he : ∀ z : Unselected sel → P,
      (∑ y : Fin n → P, A (mergeSlots sel hinj y z) * ∏ s, W s (mergeSlots sel hinj y z s)) =
      (∑ y : Fin n → P, A (mergeSlots sel hinj y z) * ∏ i, W (sel i) (y i)) *
        ∏ s : Unselected sel, W s.val (z s) := by
    intro z
    rw [sum_mul]
    apply sum_congr rfl
    intro y hy
    rw [prod_slots sel hinj]
    simp only [mergeSlots_selected,mergeSlots_unselected,mul_assoc]
  simp_rw [he]
  calc
    _ ≤ ∑ z : Unselected sel → P, K * ∏ s : Unselected sel, W s.val (z s) := by
      apply sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right (hinner z) (prod_nonneg (fun s _ => hW _ _))
    _ = _ := by rw [← mul_sum,← Fintype.prod_sum (fun s : Unselected sel => W s.val)]

end OrdinaryCorrelations.PivotSummation

end

end OAI
