import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseOuterMoments
import OAI.Combinatorics.KMedian.Sparse.SparsePreparedLaw

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw SparseGridRounding
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activation_sum (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) :
    (∑ j,activationCount D q z e j)=(D e).card*base q e+(z.2.1 e).card := by
  simp only [activationCount,sum_add_distrib,sum_ite_mem,univ_inter,sum_const,
    nsmul_eq_mul,mul_one,Nat.cast_id]

theorem raw_counts (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (z : State n m) :
    SparseSignedPreparation.raw D c (base q) z=
      (∑ e,c e*(outsideCount q z e:ℚ))-(∑ j,∑ e,(activationCount D q z e j:ℚ)) := by
  rw [sum_comm]
  simp only [SparseSignedPreparation.raw,sum_sub_distrib,← Nat.cast_sum,activation_sum,
    Nat.cast_add,Nat.cast_mul,outsideCount_cast]

def discarded (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) : ℚ :=
  ((∑ e,activationCount D q z e j):ℕ)-
    (min (∑ e,activationCount D q z e j) (Δ/2):ℕ)

def opening (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : ℚ :=
  (∑ e,c e*(outsideCount q z e:ℚ))+(∑ j,(total D q Δ z j:ℚ))

theorem raw_identity (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) :
    opening D c q Δ z=(n:ℚ)*(Δ:ℚ)+SparseSignedPreparation.raw D c (base q) z+
      ∑ j,discarded D q Δ z j := by
  have ht : ∀ j,(total D q Δ z j:ℚ)=(Δ:ℚ)-
      (min (∑ e,activationCount D q z e j) (Δ/2):ℕ) := by
    intro j
    exact Nat.cast_sub ((min_le_right _ _).trans (Nat.div_le_self _ _))
  simp only [opening,ht,raw_counts,discarded,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_sum]
  ring

theorem opening_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e)
    (a : Fin (SparseOuterLaw.law D c q hc hq).length) :
    opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] ≤
      (n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e)+3+
       ∑ j,discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j := by
  rw [raw_identity]
  have hh := (SparseOuterLaw.budget D c q hc hq a).2.2.2.2.2
  linarith only [hh]

theorem discarded_mass (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℚ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℚ)=1) :
    (g:ℝ)*(discarded D q Δ z j:ℝ)=
      (deficit D q g z j:ℝ)-min (deficit D q g z j:ℝ) (1/2) := by
  have he : (deficit D q g z j:ℝ)=(g:ℝ)*((∑ e,activationCount D q z e j):ℕ) := by
    simp only [deficit,Rat.cast_mul,Rat.cast_sum,Nat.cast_sum,← activationCount_cast,
      Rat.cast_natCast]
  rw [he,(Preparation.grid_clip (by exact_mod_cast hg) heven (by exact_mod_cast hunit)
    (∑ e,activationCount D q z e j)).1]
  simp only [discarded,Rat.cast_sub,Rat.cast_natCast,mul_sub]

end MetricKMedian.SparsePrepared
end
end

end OAI
