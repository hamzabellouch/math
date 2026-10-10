import OAI.Analysis.LipschitzHilbert.Estimates.IntGeometricSum
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! Amplitude levels of comparable support measure have a bounded
sum-to-energy ratio, independently of their number. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_class_bound (S : Finset ℤ) (mass : ℤ → ℝ) (m : ℝ)
    (hlow : ∀ i∈S, m≤mass i) (hhigh : ∀ i∈S, mass i≤2*m) :
    (∑ i∈S, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt (∑ i∈S, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
  classical
  by_cases hS : S.Nonempty
  · let j := S.max' hS
    have hj : j∈S := Finset.max'_mem S hS
    have hgeom := int_geometric_shift_sum_le (r:=(1/2:ℝ)) (by norm_num) (by norm_num) S j
    have hp (i : ℤ) (hi : i∈S) : (2:ℝ)^i=(2:ℝ)^j*(1/2:ℝ)^(i-j).natAbs := by
      have hij : i≤j := Finset.le_max' S i hi
      have hn : ((i-j).natAbs:ℤ)=j-i := by omega
      have he : (1/2:ℝ)^(i-j).natAbs=(2:ℝ)^(-((i-j).natAbs:ℤ)) := by
        simp only [zpow_neg,zpow_natCast,one_div,inv_pow]
      rw [he,hn,←zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      congr 1
      omega
    have hmass (i : ℤ) (hi : i∈S) : Real.sqrt (mass i)≤Real.sqrt 2*Real.sqrt (mass j) := by
      calc
        _ ≤ Real.sqrt (2*mass j) := Real.sqrt_le_sqrt ((hhigh i hi).trans (mul_le_mul_of_nonneg_left (hlow j hj) (by norm_num)))
        _ = _ := Real.sqrt_mul (by norm_num) _
    have hs : (∑ i∈S, (2:ℝ)^i*Real.sqrt (mass i))≤
        4*Real.sqrt 2*((2:ℝ)^j*Real.sqrt (mass j)) := by
      calc
        _ ≤ ∑ i∈S, ((2:ℝ)^j*(1/2:ℝ)^(i-j).natAbs)*(Real.sqrt 2*Real.sqrt (mass j)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hp i hi]
          exact mul_le_mul_of_nonneg_left (hmass i hi) (by positivity)
        _ = ((2:ℝ)^j*(Real.sqrt 2*Real.sqrt (mass j)))*(∑ i∈S, (1/2:ℝ)^(i-j).natAbs) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ((2:ℝ)^j*(Real.sqrt 2*Real.sqrt (mass j)))*4 :=
          mul_le_mul_of_nonneg_left (by norm_num at hgeom ⊢; exact hgeom) (by positivity)
        _ = _ := by ring
    have hterm : (2:ℝ)^j*Real.sqrt (mass j)≤
        Real.sqrt (∑ i∈S, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (fun i _ => sq_nonneg ((2:ℝ)^i*Real.sqrt (mass i))) hj
    exact hs.trans (mul_le_mul_of_nonneg_left hterm (by positivity))
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.sum_empty,Real.sqrt_zero,mul_zero,le_refl]

end LipschitzHilbert

end

end OAI
