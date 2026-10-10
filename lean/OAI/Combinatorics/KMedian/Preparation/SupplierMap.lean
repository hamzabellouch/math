import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationStars
import OAI.Combinatorics.KMedian.Preparation.SupplierAllocation

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def supplier (next : T → T) : Star I T → I ⊕ T
  | .inl i => .inl i
  | .inr (.inl st) => .inr st.2
  | .inr (.inr t) => .inr (next t)

theorem outside_supplier (next : T → T) (q : Star I T → ℝ) (i : I) :
    supplierOutside (supplier next) q i=q (.inl i) := by
  simp only [supplierOutside,Fintype.sum_sum_type,supplier,
    Sum.inl.injEq,Sum.inr_ne_inl,ite_false,sum_const_zero,add_zero,
    sum_ite_eq',mem_univ,ite_true]

theorem self_supplier_zero (P A : T → Finset I) (y : I → ℝ) (c : T → ℝ)
    (γ : ℝ) (next : T → T) (q : Star I T → ℝ) (s : T)
    (hAP : ∀ t, Disjoint (A t) (P t)) (hnext : ∀ t, next t=t → c t=0)
    (htarget : ∀ e, s ∉ targets A e → q e=0)
    (hzero : ∀ e, weight y P A c γ e=0 → q e=0) :
    supplierBundle (supplier next) q s=0 := by
  apply sum_eq_zero
  intro e _
  cases e with
  | inl i => simp only [supplier,Sum.inl_ne_inr,ite_false]
  | inr e =>
    cases e with
    | inl st =>
      dsimp only [supplier]
      by_cases ht : st.2=s
      · simp only [ht,ite_true]
        by_cases hs : st.1=s
        · apply hzero
          simp only [weight,hs,ht,disjoint_iff_inter_eq_empty.mp (hAP s),sum_empty]
        · exact htarget _ (by simpa only [targets,mem_singleton] using Ne.symm hs)
      · simp only [Sum.inr.injEq,ite_eq_right ht]
    | inr t =>
      dsimp only [supplier]
      by_cases ht : next t=s
      · simp only [ht,ite_true]
        by_cases hs : t=s
        · subst t
          apply hzero
          simp only [weight,hnext s ht,mul_zero]
        · exact htarget _ (by simpa only [targets,mem_singleton] using Ne.symm hs)
      · simp only [Sum.inr.injEq,ite_eq_right ht]

theorem ordinary_positive (P A : T → Finset I) (y : I → ℝ) (c : T → ℝ)
    (γ : ℝ) (q : Star I T → ℝ) (s u t : T)
    (hy : ∀ i, 0 ≤ y i)
    (htarget : ∀ e, s ∉ targets A e → q e=0)
    (hzero : ∀ e, weight y P A c γ e=0 → q e=0)
    (hq : 0 < q (.inr (.inl (u,t)))) :
    u=s ∧ 0 < ∑ i ∈ A s ∩ P t, y i := by
  have hus : u=s := by
    by_contra h
    have ht := htarget (.inr (.inl (u,t))) (by simpa only [targets,mem_singleton] using Ne.symm h)
    rw [ht] at hq
    exact lt_irrefl _ hq
  subst u
  refine ⟨rfl,lt_of_le_of_ne (sum_nonneg (fun i _ => hy i)) ?_⟩
  intro he
  have hz := hzero (.inr (.inl (s,t))) he.symm
  rw [hz] at hq
  exact lt_irrefl _ hq

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
