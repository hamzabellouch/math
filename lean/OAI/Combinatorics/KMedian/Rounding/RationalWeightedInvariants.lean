import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalWeightedStep

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability β p*(point (endpoint β p 0) k*point (endpoint β p 0) l)+
      (1-probability β p)*(point (endpoint β p 1) k*point (endpoint β p 1) l) ≤
        point p k*point p l := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
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

theorem endpoint_feasible (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (b : Fin 2) :
    ∀ k, 0 ≤ point (endpoint β p b) k ∧ point (endpoint β p b) k ≤ 1 := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
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
    have hh := WeightedRounding.move_bounds hpr0 hpr1 a.property.2.2 hrr ht0r ht1r
    rw [← real_move] at hh
    simp only [realPoint] at hh
    intro k
    simp only [endpoint,dite_eq_left h]
    exact ⟨by exact_mod_cast hh.1 k,by exact_mod_cast hh.2 k⟩
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_smaller (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (h : 1 < (fractional p).card) (b : Fin 2) :
    (fractional (endpoint β p b)).card < (fractional p).card := by
  let a := pair p h
  let r := β a.val.1/β a.val.2
  have hr : (0:ℝ) < r := by exact_mod_cast div_pos (hβ a.val.1) (hβ a.val.2)
  have hi : a.val.1 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.1
  have hj : a.val.2 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.2.1
  simp only [endpoint,dite_eq_left h]
  by_cases hb : b=0
  · rw [ite_eq_left hb]
    have hh := WeightedRounding.up_smaller hr a.property.2.2 hi hj
    simpa only [← real_up,← real_move,real_fractional] using hh
  · rw [ite_eq_right hb]
    have hh := WeightedRounding.down_smaller hr a.property.2.2 hi hj
    simpa only [← real_down,← Rat.cast_neg,← real_move,real_fractional] using hh

theorem endpoint_weighted (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (b : Fin 2) :
    (∑ k, β k*point (endpoint β p b) k)=∑ k, β k*point p k := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have hb : (β a.val.2:ℝ) ≠ 0 := by exact_mod_cast (hβ a.val.2).ne'
    have hh := WeightedRounding.weighted_sum (fun k => (β k:ℝ)) (realPoint p)
      (i:=a.val.1) (j:=a.val.2) hb (t:ℝ)
    rw [← Rat.cast_div,← real_move] at hh
    simp only [realPoint] at hh
    simp only [endpoint,dite_eq_left h]
    exact_mod_cast hh
  · simp only [endpoint,dite_eq_right h]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
