import Mathlib
import OAI.Combinatorics.KMedian.Optimization.LPMinimumSelection

namespace OAI


                                             
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

def before (d : Fin n → ℚ) (j i : Fin n) : Prop := d j  <  d i ∨ d j=d i ∧ j < i
instance (d : Fin n → ℚ) (j i : Fin n) : Decidable (before d j i) := by unfold before; infer_instance
def priorMass (U : Finset (Fin n)) (y d : Fin n → ℚ) (i : Fin n) : ℚ :=
  ∑ j∈U.filter (fun j => before d j i), y j

theorem first_before (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (i : Fin n) (hi : i∈U) (hne : i≠firstNearest U d hU) : before d (firstNearest U d hU) i := by
  have hd := (firstNearest_spec U d hU).2 i hi
  rcases hd.lt_or_eq with h|h
  · exact Or.inl h
  · exact Or.inr ⟨h,lt_of_le_of_ne (LPBinary.firstNearest_le U d hU i hi h.symm) hne.symm⟩

theorem not_before_first (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (i : Fin n) (hi : i∈U) : ¬before d i (firstNearest U d hU) := by
  rintro (h|⟨h,hi'⟩)
  · exact (not_lt_of_ge ((firstNearest_spec U d hU).2 i hi)) h
  · exact (not_lt_of_ge (LPBinary.firstNearest_le U d hU i hi h)) hi'

theorem priorMass_first (U : Finset (Fin n)) (y d : Fin n → ℚ) (hU : U.Nonempty) :
    priorMass U y d (firstNearest U d hU)=0 := by
  apply sum_eq_zero
  intro j hj
  exact (not_before_first U d hU j (mem_filter.mp hj).1 (mem_filter.mp hj).2).elim

theorem priorMass_erase (U : Finset (Fin n)) (y d : Fin n → ℚ) (a i : Fin n)
    (ha : a∈U) (hai : before d a i) : priorMass U y d i=priorMass (U.erase a) y d i+y a := by
  have he : (U.erase a).filter (fun j => before d j i)=(U.filter (fun j => before d j i)).erase a := by
    ext j
    simp only [mem_filter,mem_erase,and_assoc]
  unfold priorMass
  rw [he]
  exact (sum_erase_add _ y (mem_filter.mpr ⟨ha,hai⟩)).symm

theorem priorMass_nonneg (U : Finset (Fin n)) (y d : Fin n → ℚ) (i : Fin n)
    (hy : ∀ j∈U, 0 ≤ y j) : 0 ≤ priorMass U y d i :=
  sum_nonneg (fun j hj => hy j (mem_filter.mp hj).1)

theorem fill_formula (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ)
    (hy : ∀ i∈U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i∈U, y i) (i : Fin n) :
    (fill U y d t hy ht hm).amount i=
      if i∈U then min (y i) (max 0 (t-priorMass U y d i)) else 0 := by
  revert t hy
  refine U.strongInductionOn ?_
  intro U ih t hy ht hm
  by_cases hi : i∈U
  · have hU : U.Nonempty := ⟨i,hi⟩
    let a := firstNearest U d hU
    have ha : a∈U := (firstNearest_spec U d hU).1
    have hpref : priorMass U y d a=0 := priorMass_first U y d hU
    rw [ite_eq_left hi]
    by_cases hs : t ≤ y a
    · rw [fill]
      have hs' : t ≤ y (firstNearest U d hU) := hs
      simp only [dite_eq_left hU,dite_eq_left hs']
      change (if i=a then t else 0)=min (y i) (max 0 (t-priorMass U y d i))
      by_cases he : i=a
      · subst i
        rw [ite_eq_left rfl,hpref,sub_zero,max_eq_right ht,min_eq_right hs]
      · rw [ite_eq_right he]
        have hp := priorMass_nonneg (U.erase a) y d i (fun j hj => hy j (mem_of_mem_erase hj))
        rw [priorMass_erase U y d a i ha (first_before U d hU i hi he)]
        rw [max_eq_left (by linarith),min_eq_right (hy i hi)]
    · rw [fill]
      have hs' : ¬t ≤ y (firstNearest U d hU) := hs
      simp only [dite_eq_left hU,dite_eq_right hs']
      by_cases he : i=a
      · subst i
        change @Function.update (Fin n) (fun _ => ℚ) _ _ a (y a) a = _
        simp only [Function.update_self,hpref,sub_zero,max_eq_right ht,min_eq_left (le_of_not_ge hs)]
      · rw [Function.update_of_ne he]
        rw [ih (U.erase a) (erase_ssubset ha)]
        rw [ite_eq_left (mem_erase.mpr ⟨he,hi⟩)]
        rw [priorMass_erase U y d a i ha (first_before U d hU i hi he)]
        congr 2
        ring
  · rw [ite_eq_right hi]
    exact (fill U y d t hy ht hm).outside i hi

 theorem computedNearest_formula (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) (i : Fin n) :
    (computedNearest y d hy hm)[i.val]=min (y i) (max 0 (1-priorMass univ y d i)) := by
  simp only [computedNearest,Vector.getElem_ofFn,fill_formula,mem_univ,ite_true]
end MetricKMedian.Preparation
end

end OAI
