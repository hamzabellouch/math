import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedPartial
import OAI.Combinatorics.KMedian.Rounding.WeightedGridInvariant

namespace OAI


                                           
section
namespace MetricKMedian.RationalSignedStep
open RationalWeightedStep RationalGrid
variable {n : ℕ}

theorem endpoint_grid (β : Fin n → ℚ) 
    (D : ℤ) (hb : ∀ i, At D (β i)) (p : Vector ℚ n)
    (hp : ∀ i, At D (β i*point p i)) (b : Fin 2) :
    ∀ i, At D (β i*point (endpoint β p b) i) := by
  by_cases h : Active β p
  · let a := pair β p h
    let i := a.val.1
    let j := a.val.2
    let r := β i/β j
    let t := if b=0 then up p i j r else -down p i j r
    let q := move p i j r t
    have hij : i≠j := a.property.2.2.1
    have hr : r≠0 := (pair_ratio_pos β p h).ne'
    have he : endpoint β p b=q := by rw [endpoint,dite_eq_left h]
    have hw : β i*point q i+β j*point q j=β i*point p i+β j*point p j :=
      move_pair_weighted β p i j hij (pair_right_ne β p h) t
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
        convert hh using 1
        linarith
      · have haj : At D (β j*point q j) := by
          rcases hj with hj | hj
          · rw [hj,mul_zero]; exact RationalGrid.zero _
          · rw [hj,mul_one]; exact hb j
        refine ⟨?_,haj⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) haj
        convert hh using 1
        linarith
    intro k
    rw [he]
    by_cases hki : k=i
    · subst k; exact hpi.1
    by_cases hkj : k=j
    · subst k; exact hpi.2
    simpa only [q,point_move_rest _ _ _ _ hki hkj] using hp k
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_zero_weight (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2)
    (k : Fin n) (hk : β k=0) : point (endpoint β p b) k=point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    have hi : k≠a.val.1 := by
      intro he
      have hm := a.property.2.2.2
      rw [← he,hk,zero_mul] at hm
      exact lt_irrefl _ hm
    have hj : k≠a.val.2 := by
      intro he
      have hm := a.property.2.2.2
      rw [← he,hk,mul_zero] at hm
      exact lt_irrefl _ hm
    rw [endpoint,dite_eq_left h]
    exact point_move_rest _ _ _ _ hi hj _ _
  · rw [endpoint,dite_eq_right h]

end MetricKMedian.RationalSignedStep

namespace MetricKMedian.SparseWeightedPartial
open RationalWeightedStep RationalGrid
variable {n : ℕ}

theorem run_grid (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n)
    (D : ℤ) (hb : ∀ i, At D (β i)) (hp : ∀ i, At D (β i*point p i)) (t : ℕ) :
    ∀ a : Fin (run β hβ p t).length, ∀ i, At D (β i*point (run β hβ p t).states[a.val] i) := by
  induction t with
  | zero =>
    intro a
    have he : (run β hβ p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact hp
  | succ t ih =>
    apply (run β hβ p t).step_property features (probability β) (probability_unit β hβ)
      (endpoint β) (fun q => ∀ i, At D (β i*point q i))
    intro a b
    exact endpoint_grid β hβ D hb _ (ih a) b
end MetricKMedian.SparseWeightedPartial

namespace MetricKMedian.SparseSignedPartial
open RationalSignedStep RationalGrid
open RationalWeightedStep (point)
variable {n : ℕ}

theorem run_grid (β : Fin n → ℚ) (p : Vector ℚ n)
    (D : ℤ) (hb : ∀ i, At D (β i)) (hp : ∀ i, At D (β i*point p i)) (t : ℕ) :
    ∀ a : Fin (run β p t).length, ∀ i, At D (β i*point (run β p t).states[a.val] i) := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact hp
  | succ t ih =>
    apply (run β p t).step_property SparseWeightedPartial.features (probability β) (probability_unit β)
      (endpoint β) (fun q => ∀ i, At D (β i*point q i))
    intro a b
    exact endpoint_grid β D hb _ (ih a) b

theorem run_zero_weight (β : Fin n → ℚ) (p : Vector ℚ n) (t : ℕ) :
    ∀ a : Fin (run β p t).length, ∀ i, β i=0 → point (run β p t).states[a.val] i=point p i := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact fun _ _ => rfl
  | succ t ih =>
    apply (run β p t).step_property SparseWeightedPartial.features (probability β) (probability_unit β)
      (endpoint β) (fun q => ∀ i, β i=0 → point q i=point p i)
    intro a b i hi
    exact (endpoint_zero_weight β _ b i hi).trans (ih a i hi)
end MetricKMedian.SparseSignedPartial
end

end OAI
