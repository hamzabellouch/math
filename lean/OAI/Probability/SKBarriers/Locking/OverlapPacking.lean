import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finite_unit_packing {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [DecidableEq I] (S : Finset I) (u : I → E) (w : E) (b e : ℝ)
    (hb : 0<b) (he : 0≤e) (heb : e<b^2/2)
    (hw : ⟪w,w⟫_ℝ=1) (hu : ∀ i∈S,⟪u i,u i⟫_ℝ=1)
    (hpair : ∀ i∈S,∀ j∈S,i≠j → ⟪u i,u j⟫_ℝ≤e)
    (hlarge : ∀ i∈S,b<⟪u i,w⟫_ℝ) : (S.card:ℝ)<2/b^2 := by
  by_cases hS : S.Nonempty
  · let d : ℝ := S.card
    have hd : 0<d := by dsimp [d]; exact_mod_cast hS.card_pos
    have hl : d*b<⟪∑ i∈S,u i,w⟫_ℝ := by
      rw [sum_inner]
      simpa [d] using Finset.sum_lt_sum_of_nonempty hS hlarge
    have hu' : ⟪∑ i∈S,u i,∑ i∈S,u i⟫_ℝ≤d+d^2*e := by
      rw [sum_inner]
      simp_rw [inner_sum]
      calc
        _ ≤ ∑ i∈S,∑ j∈S,((if i=j then (1:ℝ) else 0)+e) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          by_cases hij : i=j
          · subst j; rw [ite_eq_left rfl,hu i hi]; linarith only [he]
          · simpa only [ite_eq_right hij,zero_add] using hpair i hi j hj hij
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_const,nsmul_eq_mul]
          simp only [Finset.sum_ite_mem,Finset.inter_self]
          simp [d]
          ring
    have hcs := real_inner_mul_inner_self_le (∑ i∈S,u i) w
    rw [hw,mul_one] at hcs
    have hls : (d*b)^2<⟪∑ i∈S,u i,w⟫_ℝ^2 := by
      exact pow_lt_pow_left₀ hl (mul_nonneg hd.le hb.le) (by decide)
    have hquad : d^2*b^2<d+d^2*e := by nlinarith only [hls,hcs,hu']
    have hdb : d*b^2<2 := by
      by_contra h
      have hd2 : 2≤d*b^2 := le_of_not_gt h
      have hpos : 0<d^2 := sq_pos_of_pos hd
      have hs := mul_lt_mul_of_pos_left heb hpos
      have hm := mul_le_mul_of_nonneg_left hd2 hd.le
      nlinarith only [hquad,hs,hm]
    exact (lt_div_iff₀ (sq_pos_of_pos hb)).mpr (by simpa [d] using hdb)
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.card_empty,Nat.cast_zero]
    positivity

def spinUnitVector {n : ℕ} (x : Config n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spin (x i)/Real.sqrt n)

theorem spinUnitVector_inner {n : ℕ} (x y : Config n) :
    ⟪spinUnitVector x,spinUnitVector y⟫_ℝ=overlap x y := by
  change (∑ i : Fin n,(spin (y i)/Real.sqrt n)*(spin (x i)/Real.sqrt n))=overlap x y
  simp only [div_mul_div_comm,← sq,Real.sq_sqrt (Nat.cast_nonneg n),← Finset.sum_div]
  exact congrArg (fun z : ℝ => z/(n:ℝ)) (Finset.sum_congr rfl (fun i _ => mul_comm _ _))

@[simp] theorem overlap_flip_first {n : ℕ} (x y : Config n) : overlap (flip x) y = -overlap x y := by
  rw [overlap_comm,overlap_flip_right,overlap_comm x y]

theorem overlap_conflict_card {n : ℕ} (hn : 0<n) {I : Type*} [DecidableEq I]
    (S : Finset I) (v : I → Config n) (w : Config n) (b e : ℝ)
    (hb : 0<b) (he : 0≤e) (heb : e<b^2/2)
    (hpair : ∀ i∈S,∀ j∈S,i≠j → |overlap (v i) (v j)|≤e)
    (hlarge : ∀ i∈S,b< |overlap (v i) w|) : (S.card:ℝ)<2/b^2 := by
  let u (i : I) : Config n := if 0≤overlap (v i) w then v i else flip (v i)
  apply finite_unit_packing S (fun i => spinUnitVector (u i)) (spinUnitVector w) b e hb he heb
  · rw [spinUnitVector_inner,overlap_self hn]
  · intro i hi; rw [spinUnitVector_inner,overlap_self hn]
  · intro i hi j hj hij
    rw [spinUnitVector_inner]
    have h := hpair i hi j hj hij
    dsimp only [u]
    split_ifs <;> (try simp only [overlap_flip_first,overlap_flip_right,neg_neg]) <;>
      linarith only [(abs_le.mp h).1,(abs_le.mp h).2]
  · intro i hi
    rw [spinUnitVector_inner]
    dsimp only [u]
    split_ifs with h
    · simpa only [abs_of_nonneg h] using hlarge i hi
    · simpa only [overlap_flip_first,abs_of_neg (lt_of_not_ge h)] using hlarge i hi

end SK.Analytic

end
end

end OAI
