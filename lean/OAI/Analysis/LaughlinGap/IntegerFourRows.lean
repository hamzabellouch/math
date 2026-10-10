import Mathlib
import OAI.Analysis.LaughlinGap.ExactRows
import OAI.Analysis.LaughlinGap.FastCoupling

namespace OAI

/-! Integer Four Rows. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

def uInt (c z T p : ℕ) : ℤ :=
  if z ≤ T then ∑ h ∈ Finset.range (p+1),
    (-1:ℤ)^(z-h) * (chooseFast z h) * (chooseFast (T-z) (p-h)) * (c:ℤ)^(p-h) else 0

lemma uFast_eq_int (c z T p : ℕ) : uFast c z T p = (uInt c z T p:ℚ) := by
  simp [uFast,uInt]

end LaughlinGap.Spin
namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def vInt (D T r p j k : ℕ) : ℤ :=
  if D ≤ T ∧ r ≤ j+k ∧ p+j+k=T then
    uInt 1 r (j+k) j * uInt 1 (D-r) (T-r) p else 0

lemma vFast_eq_int (D T r p j k : ℕ) : vFast D T r p j k = (vInt D T r p j k:ℚ) := by
  simp [vFast,vInt,uFast_eq_int]

def fourSumInteger (a : Fin 8) (D s : ℕ) (i k : Fin 9) : ℤ :=
  ∑ p : Fin 8, if h : p.val ≤ a.val+i.val ∧ a.val+i.val-p.val < 9 then
    rowAlphaInteger a p ⟨a.val+i.val-p.val,h.2⟩ *
      vInt D (a.val+i.val+k.val) s p.val (a.val+i.val-p.val) k.val *
        (2:ℤ)^((s+1)/2+p.val) else 0

lemma fourSumEval_eq_integer (a : Fin 8) (D s : ℕ) (i k : Fin 9) :
    (exactRows a).fourSumEval D s i k = (fourSumInteger a D s i k:ℚ)/10000000 := by
  simp only [RationalRow.fourSumEval,fourSumInteger,exactRows,vFast_eq_int,Int.cast_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs
  · push_cast; ring
  · simp

def fourRowWeight (D : ℕ) (a : Fin 8) (i k : Fin 9) : ℤ :=
  if D ≤ a.val+i.val+k.val then
    a.val.factorial*i.val.factorial*k.val.factorial *
      (2:ℤ)^(53-(2*(a.val+i.val+k.val)+a.val)) *
        (23-D).descFactorial (23-(a.val+i.val+k.val)) else 0

def fourMatrixDenominator (D : ℕ) : ℕ := 2^53*(23-D).factorial*100000000000000

lemma fourRowWeight_eq {D : ℕ} (hD : D ≤ 23) (a : Fin 8) (i k : Fin 9) :
    fourRowFactor a.val D i.val k.val / (100000000000000:ℚ) =
      (fourRowWeight D a i k:ℚ) / fourMatrixDenominator D := by
  by_cases h : D ≤ a.val+i.val+k.val
  · simp only [fourRowFactor,fourRowWeight,ite_eq_left h,fourMatrixDenominator]
    have hT : a.val+i.val+k.val ≤ 23 := by have := a.isLt; have := i.isLt; have := k.isLt; omega
    have he : 2*(a.val+i.val+k.val)+a.val ≤ 53 := by
      have := a.isLt; have := i.isLt; have := k.isLt; omega
    have hf : (a.val+i.val+k.val-D).factorial *
        (23-D).descFactorial (23-(a.val+i.val+k.val)) = (23-D).factorial := by
      convert Nat.factorial_mul_descFactorial (show 23-(a.val+i.val+k.val) ≤ 23-D by omega) using 1
      congr 2
      omega
    have hp : (2:ℚ)^(2*(a.val+i.val+k.val)+a.val) *
        2^(53-(2*(a.val+i.val+k.val)+a.val)) = (2:ℚ)^53 := by
      rw [← pow_add,Nat.add_sub_of_le he]
    have hfc : ((a.val+i.val+k.val-D).factorial:ℚ) *
        ((23-D).descFactorial (23-(a.val+i.val+k.val)):ℚ) = ((23-D).factorial:ℚ) := by
      exact_mod_cast hf
    push_cast
    field_simp
    nlinarith [hp,hfc]
  · simp [fourRowFactor,fourRowWeight,h]

def exactFourInteger (D u v : ℕ) : ℤ :=
  -(∑ a : Fin 8, ∑ i : Fin 9, ∑ k : Fin 9, fourRowWeight D a i k *
    fourSumInteger a D u i k * fourSumInteger a D v k i)

def exactFourEval (D u v : ℕ) : ℚ := (exactFourInteger D u v:ℚ) / fourMatrixDenominator D

lemma exactFourEval_eq {D : ℕ} (hD : D ≤ 23) (u v : ℕ) :
    (∑ a : Fin 8, (exactRows a).fourMatrixEval D u v) = exactFourEval D u v := by
  simp only [RationalRow.fourMatrixEval,fourSumEval_eq_integer,exactFourEval,exactFourInteger,
    Int.cast_neg,Int.cast_sum,Int.cast_mul,Finset.sum_neg_distrib,neg_div,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := fourRowWeight_eq hD a i k
  calc
    _ = (fourRowFactor a.val D i.val k.val/100000000000000) *
        (fourSumInteger a D u i k:ℚ) * (fourSumInteger a D v k i:ℚ) := by dsimp [exactRows]; ring
    _ = _ := by rw [hh]; ring

end LaughlinGap.RealOccupation

end

end OAI
