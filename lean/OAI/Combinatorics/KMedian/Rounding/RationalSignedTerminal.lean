import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Rounding.RationalSignedStep
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliSupport

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

def state (u : Fin n → ℚ) (p : Vector ℚ n) (ω : Fin n → Bool) : Vector ℚ n :=
  Vector.ofFn (fun i => if u i<0 then point p i else SparseBernoulli.flag ω i)

@[simp] theorem point_state (u : Fin n → ℚ) (p : Vector ℚ n) (ω : Fin n → Bool) (i : Fin n) :
    point (state u p ω) i=(if u i<0 then point p i else SparseBernoulli.flag ω i) := by
  simp only [state,point,Vector.getElem_ofFn,Fin.eta]

def terminal (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) : SparseIntegerLaw (Vector ℚ n) :=
  (SparseBernoulli.run (d := 2) (point p) hp n).map (state u p)

theorem terminal_length (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) :
    (terminal u p hp).length ≤ (n+1)^2+1 := SparseBernoulli.run_length _ _ _

theorem terminal_mean (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) :
    (terminal u p hp).moment (fun q => point q i)=point p i := by
  rw [terminal,SparseIntegerLaw.map_moment]
  by_cases hi : u i<0
  · simp only [point_state,ite_eq_left hi,SparseIntegerLaw.moment_const]
  · simp only [point_state,ite_eq_right hi,SparseBernoulli.single_moment]

theorem terminal_pair (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i j : Fin n) (hij : i≠j) :
    (terminal u p hp).moment (fun q => point q i*point q j)=point p i*point p j := by
  rw [terminal,SparseIntegerLaw.map_moment]
  by_cases hi : u i<0 <;> by_cases hj : u j<0
  · simp only [point_state,ite_eq_left hi,ite_eq_left hj,SparseIntegerLaw.moment_const]
  · simp only [point_state,ite_eq_left hi,ite_eq_right hj,SparseIntegerLaw.moment_mul,SparseBernoulli.single_moment]
  · simp only [point_state,ite_eq_right hi,ite_eq_left hj,SparseIntegerLaw.moment_mul_right,SparseBernoulli.single_moment]
  · simp only [point_state,ite_eq_right hi,ite_eq_right hj,SparseBernoulli.pair_moment _ _ _ _ hij]

theorem state_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (hpair : ¬Active u p)
    (ω : Fin n → Bool)
    (hfixed : ∀ i, i∉fractional p → SparseBernoulli.flag ω i=point p i) :
    (∀ i, 0 ≤ point (state u p ω) i ∧ point (state u p ω) i ≤ 1) ∧
    (fractional (state u p ω)).card ≤ 1 ∧
    (∑ i, u i*point (state u p ω) i) ≤ (∑ i, u i*point p i)+1 := by
  let P := (fractional p).filter (fun i => 0 < u i)
  let N := (fractional p).filter (fun i => u i < 0)
  have hP : P.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact inactive u p hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hN : N.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact inactive u p hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos_of_neg_of_neg (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hq : ∀ i, 0 ≤ point (state u p ω) i ∧ point (state u p ω) i ≤ 1 := by
    intro i
    rw [point_state]
    split_ifs
    · exact hp i
    · cases hω : ω i <;> simp [SparseBernoulli.flag,hω]
  refine ⟨hq,?_,?_⟩
  · apply le_trans (card_le_card (show fractional (state u p ω) ⊆ N from ?_)) hN
    intro i hi
    have hneg : u i<0 := by
      by_contra hn
      have hh := (mem_filter.mp hi).2
      simp only [point_state,ite_eq_right hn] at hh
      cases hω : ω i <;> simp [SparseBernoulli.flag,hω] at hh
    exact mem_filter.mpr ⟨by
      simpa only [fractional,mem_filter,mem_univ,true_and,point_state,ite_eq_left hneg] using hi,hneg⟩
  · have hz : ∀ i, i ∉ P → u i*(point (state u p ω) i-point p i)=0 := by
      intro i hi
      by_cases hn : u i<0
      · simp only [point_state,ite_eq_left hn,sub_self,mul_zero]
      by_cases he : u i=0
      · rw [he,zero_mul]
      have hp' : 0 < u i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
      have hnf : i ∉ fractional p := fun hf => hi (mem_filter.mpr ⟨hf,hp'⟩)
      simp only [point_state,ite_eq_right hn,hfixed i hnf,sub_self,mul_zero]
    have ht : ∀ i ∈ P, u i*(point (state u p ω) i-point p i) ≤ 1 := by
      intro i hi
      have hui := (mem_filter.mp hi).2
      calc
        _ ≤ u i*1 := mul_le_mul_of_nonneg_left (by linarith only [(hq i).2,(hp i).1]) hui.le
        _ ≤ 1 := by simpa only [mul_one] using hu i hui
    have hsum : (∑ i, u i*(point (state u p ω) i-point p i)) ≤ 1 := by
      rw [← sum_subset (subset_univ P) (fun i _ hi => hz i hi)]
      calc
        _ ≤ ∑ _i ∈ P, (1:ℚ) := sum_le_sum ht
        _ = (P.card:ℚ) := by simp only [sum_const,nsmul_eq_mul,mul_one]
        _ ≤ 1 := by exact_mod_cast hP
    simp only [mul_sub,sum_sub_distrib] at hsum
    linarith only [hsum]

theorem terminal_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (hpair : ¬Active u p)
    (a : Fin (terminal u p hp).length) :
    let q := (terminal u p hp).states[a.val]
    (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧ (fractional q).card ≤ 1 ∧
    (∑ i, u i*point q i) ≤ (∑ i, u i*point p i)+1 := by
  dsimp only
  change Fin (SparseBernoulli.run (d := 2) (point p) hp n).length at a
  have he := SparseIntegerLaw.map_states (SparseBernoulli.run (d := 2) (point p) hp n) (state u p) a
  change (terminal u p hp).states[a.val]=_ at he
  rw [he]
  apply state_spec u p hp hu hpair
  intro i hi
  apply SparseBernoulli.fixed _ hp a i
  have hr := MarginalRounding.nonfractional_integral
    (fun i => by change 0 ≤ (point p i : ℝ); exact_mod_cast (hp i).1 : ∀ i, 0 ≤ realPoint p i)
    (fun i => by change (point p i : ℝ) ≤ 1; exact_mod_cast (hp i).2 : ∀ i, realPoint p i ≤ 1)
    (show i ∉ MarginalRounding.fractional (realPoint p) by simpa only [real_fractional] using hi)
  change (point p i : ℝ)=0 ∨ (point p i : ℝ)=1 at hr
  exact_mod_cast hr

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
