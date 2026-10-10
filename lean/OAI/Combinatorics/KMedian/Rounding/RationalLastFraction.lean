import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalWeightedInvariants

namespace OAI

section
section
namespace MetricKMedian.RationalLastFraction
open Finset RationalWeightedStep
variable {n : ℕ}

def pick (p : Vector ℚ n) (h : (fractional p).Nonempty) : Fin n := (fractional p).min' h

theorem pick_mem (p : Vector ℚ n) (h : (fractional p).Nonempty) : pick p h ∈ fractional p :=
  min'_mem _ _

def probability (p : Vector ℚ n) : ℚ :=
  if h : (fractional p).Nonempty then point p (pick p h) else 0

def endpoint (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : (fractional p).Nonempty then
    Vector.ofFn (fun k => if k=pick p h then (if b=0 then 1 else 0) else point p k)
  else p

theorem probability_unit (p : Vector ℚ n) : 0 ≤ probability p ∧ probability p ≤ 1 := by
  unfold probability
  split_ifs with h
  · have hh := (mem_filter.mp (pick_mem p h)).2
    exact ⟨hh.1.le,hh.2.le⟩
  · exact ⟨le_rfl,by norm_num⟩

theorem endpoint_mean (p : Vector ℚ n) (k : Fin n) :
    probability p*point (endpoint p 0) k+
      (1-probability p)*point (endpoint p 1) k=point p k := by
  by_cases h : (fractional p).Nonempty
  · simp only [probability,endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    by_cases hi : k=pick p h
    · subst k; simp only [ite_true]; ring
    · simp only [ite_eq_right hi]; ring
  · simp only [probability,endpoint,dite_eq_right h]; ring

theorem endpoint_pair (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability p*(point (endpoint p 0) k*point (endpoint p 0) l)+
      (1-probability p)*(point (endpoint p 1) k*point (endpoint p 1) l)=point p k*point p l := by
  by_cases h : (fractional p).Nonempty
  · simp only [probability,endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    by_cases hk : k=pick p h
    · have hl : l ≠ pick p h := by intro he; exact hkl (hk.trans he.symm)
      simp only [hk,ite_true,ite_eq_right hl]
      ring
    · by_cases hl : l=pick p h
      · simp only [hl,ite_true,ite_eq_right hk]; ring
      · simp only [ite_eq_right hk,ite_eq_right hl]; ring
  · simp only [probability,endpoint,dite_eq_right h]; ring

theorem nonfractional (p : Vector ℚ n)
    (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (k : Fin n)
    (hk : k ∉ fractional p) : point p k=0 ∨ point p k=1 := by
  have h := hp k
  simp only [fractional,mem_filter,mem_univ,true_and,not_and_or,not_lt] at hk
  rcases hk with hk | hk
  · exact Or.inl (le_antisymm hk h.1)
  · exact Or.inr (le_antisymm h.2 hk)

theorem endpoint_integral (p : Vector ℚ n)
    (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1)
    (hsmall : (fractional p).card ≤ 1) (b : Fin 2) (k : Fin n) :
    point (endpoint p b) k=0 ∨ point (endpoint p b) k=1 := by
  by_cases h : (fractional p).Nonempty
  · simp only [endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    by_cases hk : k=pick p h
    · simp only [ite_eq_left hk]; split_ifs <;> simp
    · simp only [ite_eq_right hk]
      apply nonfractional p hp k
      intro hm
      exact hk (card_le_one.mp hsmall k hm (pick p h) (pick_mem p h))
  · simp only [endpoint,dite_eq_right h]
    apply nonfractional p hp
    exact fun hm => h ⟨k,hm⟩

theorem endpoint_noise (p : Vector ℚ n) (β : Fin n → ℚ) {M : ℚ}
    (hβ0 : ∀ k, 0 ≤ β k) (hβM : ∀ k, β k ≤ M) (hM : 0 ≤ M) (b : Fin 2) :
    |(∑ k, β k*point (endpoint p b) k)-(∑ k, β k*point p k)| ≤ M := by
  by_cases h : (fractional p).Nonempty
  · simp only [endpoint,dite_eq_left h]
    let i := pick p h
    have hi := (mem_filter.mp (pick_mem p h)).2
    rw [← sum_sub_distrib]
    have hid : (∑ k, (β k*point (Vector.ofFn
        (fun k => if k=pick p h then (if b=0 then 1 else 0) else point p k)) k-β k*point p k))=
        β i*((if b=0 then 1 else 0)-point p i) := by
      rw [sum_eq_single i]
      · simp only [point,Vector.getElem_ofFn,Fin.eta,i,ite_true]
        ring
      · intro k _ hki
        simp only [point,Vector.getElem_ofFn,Fin.eta,show k ≠ pick p h from hki,ite_false,sub_self]
      · intro hh; exact False.elim (hh (mem_univ i))
    rw [hid,abs_mul,abs_of_nonneg (hβ0 i)]
    have herr : |(if b=0 then (1:ℚ) else 0)-point p i| ≤ 1 := by
      apply abs_le.mpr
      split_ifs <;> constructor <;> dsimp only [i] <;> linarith only [hi.1,hi.2]
    exact (mul_le_mul_of_nonneg_left herr (hβ0 i)).trans (by simpa only [mul_one] using hβM i)
  · simpa only [endpoint,dite_eq_right h,sub_self,abs_zero] using hM

end MetricKMedian.RationalLastFraction
end
end

end OAI
