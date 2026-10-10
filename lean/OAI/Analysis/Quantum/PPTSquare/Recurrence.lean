import OAI.Analysis.Quantum.PPTSquare.Multiplication

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
variable {K : Type*} [Field K]
def lowMon (t : Fin 3 → K) (j : Fin 20) : K := ∏ a : Fin 3, t a ^ lowExp j a
def highMon (t : Fin 3 → K) (j : Fin 15) : K := ∏ a : Fin 3, t a ^ highExp j a
lemma lowMon_zero (t : Fin 3 → K) : lowMon t 0 = 1 := by simp [lowMon, lowExp, Fin.prod_univ_succ]
lemma low_step0 (t : Fin 3 → K) (j : Fin 10) : lowMon t (lowNext 0 j) = t 0 * lowMon t (j.castLE (by decide)) := by
  fin_cases j <;> norm_num [lowMon, lowExp, lowNext, Fin.prod_univ_succ] <;> ring
lemma high_step0 (t : Fin 3 → K) (j : Fin 10) : highMon t (highNext 0 j) = t 0 * lowMon t (j.natAdd 10) := by
  fin_cases j <;> norm_num [highMon, lowMon, lowExp, highExp, highNext, Fin.prod_univ_succ] <;> ring
lemma low_step1 (t : Fin 3 → K) (j : Fin 10) : lowMon t (lowNext 1 j) = t 1 * lowMon t (j.castLE (by decide)) := by
  fin_cases j <;> norm_num [lowMon, lowExp, lowNext, Fin.prod_univ_succ] <;> ring
lemma high_step1 (t : Fin 3 → K) (j : Fin 10) : highMon t (highNext 1 j) = t 1 * lowMon t (j.natAdd 10) := by
  fin_cases j <;> norm_num [highMon, lowMon, lowExp, highExp, highNext, Fin.prod_univ_succ] <;> ring
lemma low_step2 (t : Fin 3 → K) (j : Fin 10) : lowMon t (lowNext 2 j) = t 2 * lowMon t (j.castLE (by decide)) := by
  fin_cases j <;> norm_num [lowMon, lowExp, lowNext, Fin.prod_univ_succ] <;> ring
lemma high_step2 (t : Fin 3 → K) (j : Fin 10) : highMon t (highNext 2 j) = t 2 * lowMon t (j.natAdd 10) := by
  fin_cases j <;> norm_num [highMon, lowMon, lowExp, highExp, highNext, Fin.prod_univ_succ] <;> ring
lemma low_step (t : Fin 3 → K) (a : Fin 3) (j : Fin 10) : lowMon t (lowNext a j) = t a * lowMon t (j.castLE (by decide)) := by
  fin_cases a
  · exact low_step0 t j
  · exact low_step1 t j
  · exact low_step2 t j
lemma high_step (t : Fin 3 → K) (a : Fin 3) (j : Fin 10) : highMon t (highNext a j) = t a * lowMon t (j.natAdd 10) := by
  fin_cases a
  · exact high_step0 t j
  · exact high_step1 t j
  · exact high_step2 t j
lemma low_recursion (v : Fin 20 → K) (t : Fin 3 → K)
    (h : ∀ a : Fin 3, ∀ j : Fin 10, v (lowNext a j) = t a * v (j.castLE (by decide))) :
    ∀ j, v j = lowMon t j * v 0 := by
  have h0 : v 0 = lowMon t 0 * v 0 := by rw [lowMon_zero, one_mul]
  have h1 : v 1 = lowMon t 1 * v 0 := by
    have hh := h 2 0
    change v 1 = t 2 * v 0 at hh
    rw [hh, h0]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]
  have h2 : v 2 = lowMon t 2 * v 0 := by
    have hh := h 1 0
    change v 2 = t 1 * v 0 at hh
    rw [hh, h0]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]
  have h3 : v 3 = lowMon t 3 * v 0 := by
    have hh := h 0 0
    change v 3 = t 0 * v 0 at hh
    rw [hh, h0]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]
  have h4 : v 4 = lowMon t 4 * v 0 := by
    have hh := h 2 1
    change v 4 = t 2 * v 1 at hh
    rw [hh, h1]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h5 : v 5 = lowMon t 5 * v 0 := by
    have hh := h 1 1
    change v 5 = t 1 * v 1 at hh
    rw [hh, h1]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h6 : v 6 = lowMon t 6 * v 0 := by
    have hh := h 1 2
    change v 6 = t 1 * v 2 at hh
    rw [hh, h2]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h7 : v 7 = lowMon t 7 * v 0 := by
    have hh := h 0 1
    change v 7 = t 0 * v 1 at hh
    rw [hh, h1]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h8 : v 8 = lowMon t 8 * v 0 := by
    have hh := h 0 2
    change v 8 = t 0 * v 2 at hh
    rw [hh, h2]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h9 : v 9 = lowMon t 9 * v 0 := by
    have hh := h 0 3
    change v 9 = t 0 * v 3 at hh
    rw [hh, h3]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h10 : v 10 = lowMon t 10 * v 0 := by
    have hh := h 2 4
    change v 10 = t 2 * v 4 at hh
    rw [hh, h4]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h11 : v 11 = lowMon t 11 * v 0 := by
    have hh := h 1 4
    change v 11 = t 1 * v 4 at hh
    rw [hh, h4]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h12 : v 12 = lowMon t 12 * v 0 := by
    have hh := h 1 5
    change v 12 = t 1 * v 5 at hh
    rw [hh, h5]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h13 : v 13 = lowMon t 13 * v 0 := by
    have hh := h 1 6
    change v 13 = t 1 * v 6 at hh
    rw [hh, h6]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h14 : v 14 = lowMon t 14 * v 0 := by
    have hh := h 0 4
    change v 14 = t 0 * v 4 at hh
    rw [hh, h4]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h15 : v 15 = lowMon t 15 * v 0 := by
    have hh := h 0 5
    change v 15 = t 0 * v 5 at hh
    rw [hh, h5]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h16 : v 16 = lowMon t 16 * v 0 := by
    have hh := h 0 6
    change v 16 = t 0 * v 6 at hh
    rw [hh, h6]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h17 : v 17 = lowMon t 17 * v 0 := by
    have hh := h 0 7
    change v 17 = t 0 * v 7 at hh
    rw [hh, h7]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h18 : v 18 = lowMon t 18 * v 0 := by
    have hh := h 0 8
    change v 18 = t 0 * v 8 at hh
    rw [hh, h8]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  have h19 : v 19 = lowMon t 19 * v 0 := by
    have hh := h 0 9
    change v 19 = t 0 * v 9 at hh
    rw [hh, h9]
    norm_num [lowMon, lowExp, Fin.prod_univ_succ]; ring
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
lemma highNext_surjective : Function.Surjective (fun p : Fin 3 × Fin 10 => highNext p.1 p.2) := by decide
end PencilAlgebra

end

end OAI
