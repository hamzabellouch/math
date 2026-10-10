import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalWeightedStep
import OAI.Combinatorics.KMedian.Optimization.GradientDenominator

namespace OAI


                                             
section
namespace MetricKMedian.RationalGrid

theorem add {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (a+b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A+B,by rw [Int.cast_add,add_div]⟩

theorem mul {D E : ℤ} {a b : ℚ} (ha : At D a) (hb : At E b) : At (D*E) (a*b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A*B,by rw [Int.cast_mul,Int.cast_mul,mul_div_mul_comm]⟩

end MetricKMedian.RationalGrid

namespace MetricKMedian.RationalWeightedStep
open Finset RationalGrid
variable {n : ℕ}

theorem point_move_self (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r t : ℚ) :
    point (move p i j r t) i=point p i+t := by
  simp [point,move,hij]
theorem point_move_other (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r t : ℚ) :
    point (move p i j r t) j=point p j-t*r := by
  simp [point,move,Ne.symm hij,sub_eq_add_neg]
theorem point_move_rest (p : Vector ℚ n) (i j k : Fin n) (hki : k≠i) (hkj : k≠j) (r t : ℚ) :
    point (move p i j r t) k=point p k := by
  simp [point,move,hki,hkj]

theorem move_pair_weighted (β : Fin n → ℚ) (p : Vector ℚ n) (i j : Fin n)
    (hij : i≠j) (hj : β j ≠ 0) (t : ℚ) :
    β i*point (move p i j (β i/β j) t) i+
      β j*point (move p i j (β i/β j) t) j=β i*point p i+β j*point p j := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  field_simp
  ring

theorem up_integral (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r : ℚ) (hr : r≠0) :
    point (move p i j r (up p i j r)) i=1 ∨ point (move p i j r (up p i j r)) j=0 := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  unfold up
  rcases le_total (1-point p i) (point p j/r) with h | h
  · left; rw [min_eq_left h]; ring
  · right; rw [min_eq_right h,div_mul_cancel₀ _ hr,sub_self]

theorem down_integral (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r : ℚ) (hr : r≠0) :
    point (move p i j r (-down p i j r)) i=0 ∨ point (move p i j r (-down p i j r)) j=1 := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  unfold down
  rcases le_total (point p i) ((1-point p j)/r) with h | h
  · left; rw [min_eq_left h]; ring
  · right; rw [min_eq_right h,neg_mul,div_mul_cancel₀ _ hr]; ring

theorem endpoint_grid (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (D : ℤ) (hb : ∀ i, At D (β i)) (p : Vector ℚ n)
    (hp : ∀ i, At D (β i*point p i)) (b : Fin 2) :
    ∀ i, At D (β i*point (endpoint β p b) i) := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let i := a.val.1
    let j := a.val.2
    let r := β i/β j
    let t := if b=0 then up p i j r else -down p i j r
    let q := move p i j r t
    have hij : i≠j := a.property.2.2
    have hr : r≠0 := (div_pos (hβ i) (hβ j)).ne'
    have he : endpoint β p b=q := by rw [endpoint,dite_eq_left h]
    have hw : β i*point q i+β j*point q j=β i*point p i+β j*point p j :=
      move_pair_weighted β p i j hij (hβ j).ne' t
    have hint : (point q i=0 ∨ point q i=1) ∨ (point q j=0 ∨ point q j=1) := by
      by_cases hb0 : b=0
      · have hh := up_integral p i j hij r hr
        simpa only [q,t,hb0,ite_true] using hh.imp (fun hi => Or.inr hi) (fun hj => Or.inl hj)
      · have hh := down_integral p i j hij r hr
        simpa only [q,t,hb0,ite_false] using hh.imp (fun hi => Or.inl hi) (fun hj => Or.inr hj)
    have hpi : At D (β i*point q i) ∧ At D (β j*point q j) := by
      rcases hint with hi | hj
      · have hai : At D (β i*point q i) := by
          rcases hi with hi | hi
          · rw [hi,mul_zero]; exact RationalGrid.zero _
          · rw [hi,mul_one]; exact hb i
        refine ⟨hai,?_⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) hai
        convert hh using 1; linarith
      · have haj : At D (β j*point q j) := by
          rcases hj with hj | hj
          · rw [hj,mul_zero]; exact RationalGrid.zero _
          · rw [hj,mul_one]; exact hb j
        refine ⟨?_,haj⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) haj
        convert hh using 1; linarith
    intro k
    rw [he]
    by_cases hki : k=i
    · subst k; exact hpi.1
    by_cases hkj : k=j
    · subst k; exact hpi.2
    simpa only [q,point_move_rest _ _ _ _ hki hkj] using hp k
  · simpa only [endpoint,dite_eq_right h] using hp

end MetricKMedian.RationalWeightedStep
end

end OAI
