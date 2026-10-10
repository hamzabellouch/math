import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalWeightedInvariants

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

def pairs (u : Fin n → ℚ) (p : Vector ℚ n) : Finset (Fin (n*n)) :=
  univ.filter (fun z => let a := finProdFinEquiv.symm z;
    a.1∈fractional p ∧ a.2∈fractional p ∧ a.1≠a.2 ∧ 0<u a.1*u a.2)

def Active (u : Fin n → ℚ) (p : Vector ℚ n) : Prop := (pairs u p).Nonempty
instance (u : Fin n → ℚ) (p : Vector ℚ n) : Decidable (Active u p) :=
  inferInstanceAs (Decidable (pairs u p).Nonempty)

def pair (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    {a : Fin n × Fin n // a.1∈fractional p ∧ a.2∈fractional p ∧
      a.1≠a.2 ∧ 0<u a.1*u a.2} :=
  ⟨finProdFinEquiv.symm ((pairs u p).min' h), by
    have hh := min'_mem (pairs u p) h
    exact (mem_filter.mp hh).2⟩

theorem pair_ratio_pos (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    0<u (pair u p h).val.1/u (pair u p h).val.2 := by
  rcases mul_pos_iff.mp (pair u p h).property.2.2.2 with h | h
  · exact div_pos h.1 h.2
  · exact div_pos_of_neg_of_neg h.1 h.2

theorem pair_right_ne (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    u (pair u p h).val.2≠0 := by
  intro hz
  have hh := (pair u p h).property.2.2.2
  rw [hz,mul_zero] at hh
  exact lt_irrefl _ hh

theorem inactive (u : Fin n → ℚ) (p : Vector ℚ n) (h : ¬Active u p) :
    ∀ i∈fractional p, ∀ j∈fractional p, i≠j → ¬0<u i*u j := by
  intro i hi j hj hij hs
  apply h
  refine ⟨finProdFinEquiv (i,j),?_⟩
  simp only [pairs,mem_filter,mem_univ,true_and,Equiv.symm_apply_apply]
  exact ⟨hi,hj,hij,hs⟩

def probability (β : Fin n → ℚ) (p : Vector ℚ n) : ℚ :=
  if h : Active β p then
    let a := pair β p h
    let r := β a.val.1/β a.val.2
    down p a.val.1 a.val.2 r/(up p a.val.1 a.val.2 r+down p a.val.1 a.val.2 r)
  else 0

def endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : Active β p then
    let a := pair β p h
    let r := β a.val.1/β a.val.2
    move p a.val.1 a.val.2 r (if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r)
  else p

theorem probability_unit (β : Fin n → ℚ) (p : Vector ℚ n) :
    0 ≤ probability β p ∧ probability β p ≤ 1 := by
  unfold probability
  split_ifs with h
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    exact ⟨(div_pos hd (add_pos hu hd)).le,(div_le_one (add_pos hu hd)).mpr (by linarith)⟩
  · exact ⟨le_rfl,by norm_num⟩

theorem endpoint_mean (β : Fin n → ℚ) (p : Vector ℚ n) (k : Fin n) :
    probability β p*point (endpoint β p 0) k+
      (1-probability β p)*point (endpoint β p 1) k=point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_mean (realPoint p) a.val.1 a.val.2 k (r:ℝ) hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add]

theorem endpoint_pair (β : Fin n → ℚ) 
    (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability β p*(point (endpoint β p 0) k*point (endpoint β p 0) l)+
      (1-probability β p)*(point (endpoint β p 1) k*point (endpoint β p 1) l) ≤
        point p k*point p l := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hrr : (0:ℝ) ≤ r := by exact_mod_cast hr.le
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_pair (realPoint p) a.val.1 a.val.2 hkl hrr hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add,le_refl]

theorem endpoint_feasible (β : Fin n → ℚ) 
    (p : Vector ℚ n) (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (b : Fin 2) :
    ∀ k, 0 ≤ point (endpoint β p b) k ∧ point (endpoint β p b) k ≤ 1 := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hpr0 : ∀ k, 0 ≤ realPoint p k := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).1
    have hpr1 : ∀ k, realPoint p k ≤ 1 := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).2
    have hrr : (0:ℝ) < r := by exact_mod_cast hr
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have ht0 : -down p a.val.1 a.val.2 r ≤ t := by dsimp only [t]; split_ifs <;> linarith
    have ht1 : t ≤ up p a.val.1 a.val.2 r := by dsimp only [t]; split_ifs <;> linarith
    have ht0r : -WeightedRounding.down (realPoint p) a.val.1 a.val.2 (r:ℝ) ≤ (t:ℝ) := by
      rw [← real_down,← Rat.cast_neg]; exact_mod_cast ht0
    have ht1r : (t:ℝ) ≤ WeightedRounding.up (realPoint p) a.val.1 a.val.2 (r:ℝ) := by
      rw [← real_up]; exact_mod_cast ht1
    have hh := WeightedRounding.move_bounds hpr0 hpr1 a.property.2.2.1 hrr ht0r ht1r
    rw [← real_move] at hh
    simp only [realPoint] at hh
    intro k
    simp only [endpoint,dite_eq_left h]
    exact ⟨by exact_mod_cast hh.1 k,by exact_mod_cast hh.2 k⟩
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_smaller (β : Fin n → ℚ) 
    (p : Vector ℚ n) (h : Active β p) (b : Fin 2) :
    (fractional (endpoint β p b)).card < (fractional p).card := by
  let a := pair β p h
  let r := β a.val.1/β a.val.2
  have hr : (0:ℝ) < r := by exact_mod_cast pair_ratio_pos β p h
  have hi : a.val.1 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.1
  have hj : a.val.2 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.2.1
  simp only [endpoint,dite_eq_left h]
  by_cases hb : b=0
  · rw [ite_eq_left hb]
    have hh := WeightedRounding.up_smaller hr a.property.2.2.1 hi hj
    simpa only [← real_up,← real_move,real_fractional] using hh
  · rw [ite_eq_right hb]
    have hh := WeightedRounding.down_smaller hr a.property.2.2.1 hi hj
    simpa only [← real_down,← Rat.cast_neg,← real_move,real_fractional] using hh

theorem endpoint_weighted (β : Fin n → ℚ) 
    (p : Vector ℚ n) (b : Fin 2) :
    (∑ k, β k*point (endpoint β p b) k)=∑ k, β k*point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have hb : (β a.val.2:ℝ) ≠ 0 := by exact_mod_cast pair_right_ne β p h
    have hh := WeightedRounding.weighted_sum (fun k => (β k:ℝ)) (realPoint p)
      (i:=a.val.1) (j:=a.val.2) hb (t:ℝ)
    rw [← Rat.cast_div,← real_move] at hh
    simp only [realPoint] at hh
    simp only [endpoint,dite_eq_left h]
    exact_mod_cast hh
  · simp only [endpoint,dite_eq_right h]

end MetricKMedian.RationalSignedStep
end
end

end OAI
