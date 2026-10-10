import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer
import OAI.NumberTheory.Ostmann.Construction.GiantCellPriorIdentity

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def integerPivotCell (G : ℝ) : Finset ℕ := Finset.Ioc 0 ⌈Real.exp (G+1)⌉₊

theorem logCellPrior_pivot_mean (G : ℝ) (hZ : 0<logCellMass G ∅)
    (u : ℕ) (R : ℕ → ℝ) :
    (logCellPrior G ∅ hZ).mean (fun p => (p:ℕ)*u*R p) =
      (logCellMass G ∅)⁻¹ * ∑ p∈logCellPrimes G,
        (u:ℝ)*Ostmann.smoothPartition (Real.log p-G)*R p := by
  have he := logCellPrior_mean_indicator G hZ (logCellPrimes G)
    (fun p hp => (Finset.mem_filter.mp hp).2) (fun p => (p:ℝ)*u*R p)
  have hi (p : LogCellSample G ∅) :
      (if (p:ℕ)∈logCellPrimes G then (p:ℕ)*u*R p else 0)=(p:ℕ)*u*R p := by
    have hp := Finset.mem_sdiff.mp p.property |>.1
    simp only [hp,ite_true]
  simp_rw [hi] at he
  rw [he]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  unfold logCellWeight
  field_simp

theorem logCellPrior_extend_integer_pivots (G : ℝ) (hZ : 0<logCellMass G ∅)
    (u : ℕ) (R : ℕ → ℝ) (hR : ∀p∈integerPivotCell G,0≤R p) :
    (logCellPrior G ∅ hZ).mean (fun p => (p:ℕ)*u*R p) ≤
      (logCellMass G ∅)⁻¹ * ∑ p∈integerPivotCell G,
        (u:ℝ)*Ostmann.smoothPartition (Real.log p-G)*R p := by
  rw [logCellPrior_pivot_mean]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro p hp hnot
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Ostmann.smoothPartition_nonneg _)) (hR p hp)

theorem logCell_inverse_eq_exp_cost (G : ℝ) (hZ : 0<logCellMass G ∅) :
    (logCellMass G ∅)⁻¹=Real.exp (-Real.log (logCellMass G ∅)) := by
  rw [Real.exp_neg,Real.exp_log hZ]

def integerPivotSquare (u : ℕ) (B : (p : ℕ) → ZMod (p*u) → ℂ) (p : ℕ) : ℝ :=
  if h : p*u=0 then 0 else letI : NeZero (p*u) := ⟨h⟩
    ∑ t : ZMod (p*u),‖B p t‖^2

theorem integerPivotSquare_nonneg (u : ℕ) (B : (p : ℕ) → ZMod (p*u) → ℂ) (p : ℕ) :
    0 ≤ integerPivotSquare u B p := by
  unfold integerPivotSquare
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem logCellPrior_extend_square_rows (G : ℝ) (hZ : 0<logCellMass G ∅)
    (u : ℕ) (B : (p : ℕ) → ZMod (p*u) → ℂ) :
    (logCellPrior G ∅ hZ).mean (fun p => (p:ℕ)*u*integerPivotSquare u B p) ≤
      Real.exp (-Real.log (logCellMass G ∅)) * ∑ p∈integerPivotCell G,
        (u:ℝ)*Ostmann.smoothPartition (Real.log p-G)*integerPivotSquare u B p := by
  rw [← logCell_inverse_eq_exp_cost G hZ]
  exact logCellPrior_extend_integer_pivots G hZ u (integerPivotSquare u B)
    (fun p hp => integerPivotSquare_nonneg u B p)

end Ostmann.Construction

end

end OAI
