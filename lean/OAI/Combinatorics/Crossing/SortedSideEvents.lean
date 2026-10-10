import OAI.Combinatorics.Crossing.AffineSideEvents
import Mathlib.Data.Finset.Sort

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem exists_sorted_permutation (n : ℕ) (r : Fin n → ℝ) (hr : Function.Injective r) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (r ∘ e) := by
  let e := @Fintype.orderIsoFinOfCardEq (Fin n) (LinearOrder.lift' r hr)
    inferInstance n (Fintype.card_fin n)
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  exact @OrderIso.strictMono (Fin n) (Fin n) inferInstance
    (LinearOrder.lift' r hr).toPreorder e i j hij

theorem sum_affine_side_events_unordered (n : ℕ) (r b : Fin n → ℝ)
    (hr : Function.Injective r) (hb : ∀ i, b i ≠ 0) (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, if 0<r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0) =
      (∏ i, positiveIndicator (b i*(1-r i))) - ∏ i, positiveIndicator (b i*(0-r i)) := by
  obtain ⟨e,he⟩ := exists_sorted_permutation n r hr
  have h := sum_affine_side_events n (r ∘ e) (b ∘ e) he
    (fun i => hb (e i)) (fun i => h0 (e i)) (fun i => h1 (e i))
  simp only [Function.comp_apply] at h
  have hprod : ∀ i, (∏ j : Fin n, if j=i then (1 : ℝ) else
      positiveIndicator (b (e j)*(r (e i)-r (e j)))) =
      ∏ j : Fin n, if j=e i then 1 else positiveIndicator (b j*(r (e i)-r j)) := by
    intro i
    rw [← Equiv.prod_comp e (fun j => if j=e i then (1 : ℝ) else positiveIndicator (b j*(r (e i)-r j)))]
    simp only [e.injective.eq_iff]
  simp_rw [hprod] at h
  rw [Equiv.sum_comp e (fun i => if 0<r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0),
    Equiv.prod_comp e (fun i => positiveIndicator (b i*(1-r i))),
    Equiv.prod_comp e (fun i => positiveIndicator (b i*(0-r i)))] at h
  exact h

theorem prod_positiveIndicator {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∏ i, positiveIndicator (f i)) = if ∀ i, 0<f i then 1 else 0 := by
  classical
  by_cases h : ∀ i, 0<f i
  · simp [positiveIndicator,h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (not_lt.mpr hi))

end Zarankiewicz

end

end OAI
