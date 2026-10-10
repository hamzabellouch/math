import Mathlib
import OAI.Analysis.LaughlinFock.AllowanceOrbit
import OAI.Analysis.LaughlinFock.FourHighest

namespace OAI

/-! Four Retained. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem retainedFourTarget_copy_sum {Q : ℕ} (hQ : 24 ≤ Q) :
    exteriorLift Q 4 (retainedFourTarget Q 23) =
      ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
        targetCopy D r s • fourCopyLift Q D r s := by
  classical
  let f (z : ℕ) := ∑ k ∈ Finset.range ((2*Q-2)+(2*Q-2)-2*z+1),
    (fourCoupledAnnihilator Q z k)ᴴ * fourCoupledAnnihilator Q z k
  have h1 : exteriorLift Q 4 (retainedFourTarget Q 23) =
      ∑ z ∈ Finset.range (2*Q-2+1), if z+1 ≤ 23 then f z else 0 := by
    rw [retainedFourTarget_lift]
    change (∑ c : (z : Fin (min (2*Q-2) (2*Q-2)+1)) ×
      Fin ((2*Q-2)+(2*Q-2)-2*z.val+1), if c.1.val+1 ≤ 23 then
        (fourCoupledAnnihilator Q c.1.val c.2.val)ᴴ *
          fourCoupledAnnihilator Q c.1.val c.2.val else 0) = _
    rw [Fintype.sum_sigma, min_self]
    rw [← Fin.sum_univ_eq_sum_range (fun z => if z+1 ≤ 23 then f z else 0)]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z.val+1 ≤ 23
    · simp only [hz, ite_true]
      exact Fin.sum_univ_eq_sum_range (fun k =>
        (fourCoupledAnnihilator Q z.val k)ᴴ * fourCoupledAnnihilator Q z.val k) _
    · simp only [hz, ite_false, Finset.sum_const_zero]
  rw [h1, ← Finset.sum_filter]
  have he : (Finset.range (2*Q-2+1)).filter (fun z => z+1 ≤ 23) = Finset.range 23 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  apply Finset.sum_bij (fun z _ => z+1)
  · intro z hz
    have := Finset.mem_range.mp hz
    simp only [Finset.mem_Icc]
    omega
  · intro z hz w hw hzw
    omega
  · intro D hD
    have hD' := Finset.mem_Icc.mp hD
    refine ⟨D-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro z hz
    have hz' := Finset.mem_range.mp hz
    rw [targetCopy_sum (by omega : 1 ≤ z+1),
      fourCopyLift_first (by omega : 1 ≤ Q) (by omega : 1 ≤ z+1) (by omega : z+1 ≤ Q)]
    have hd : (2*Q-2)+(2*Q-2)-2*z+1 = fourSpinDegree Q (z+1)+1 := by
      dsimp [fourSpinDegree]
      omega
    simp only [Nat.add_sub_cancel, f, hd]

 

theorem averagedRowsFour_copy_sum {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 24 ≤ Q) :
    averagedRowsFour (by omega : 8 ≤ Q) rows =
      ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
        (((2*Q-1 : ℕ) : ℂ) *
          ((∑ i, rowFourTrace Q D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ) /
          (fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s := by
  rw [averagedRowsFour, map_sum]
  simp_rw [fockAverage_rowFourBody hQ]
  simp only [Finset.smul_sum, smul_smul, ← mul_div_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_smul]
  simp only [← Finset.sum_div, ← Finset.mul_sum, ← Complex.ofReal_sum]

 
theorem fourCopyAllowance_copy_sum {Q : ℕ} (hQ : 24 ≤ Q) :
    fourCopyAllowance Q = ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
      ((((2*Q-1 : ℕ) : ℂ) * (1 : Matrix (CopyLabel D) (CopyLabel D) ℂ) r s) /
        (fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s := by
  classical
  unfold fourCopyAllowance
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hd : D ≤ Q := by have := (Finset.mem_Icc.mp hD).2; omega
  rw [map_sum, Finset.smul_sum]
  simp_rw [fockAverage_highestFour (by omega : 1 ≤ Q) hd]
  apply Finset.sum_congr rfl
  intro r _
  simp [Matrix.one_apply, ite_smul, smul_smul, div_eq_mul_inv]

 

theorem fourSpinRatio_common_dimensions {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    (fourSpinRatio Q D : ℂ) = (fourSpinDegree Q D+1 : ℂ) / ((2*Q-1 : ℕ) : ℂ) := by
  rw [fourSpinRatio_eq_dimensions hQ hD, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_natCast]
  have hd : 4*Q-1-2*D = fourSpinDegree Q D+1 := by
    dsimp [fourSpinDegree]
    omega
  rw [hd, Nat.cast_add_one]

 

theorem averagedFourComparison_eq {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) {Q : ℕ} (hQ : 24 ≤ Q) :
    averagedFourComparison rows ε Q =
      exteriorLift Q 4 (retainedFourTarget Q 23) -
        averagedRowsFour (by omega : 8 ≤ Q) rows + ε • fourCopyAllowance Q := by
  classical
  rw [retainedFourTarget_copy_sum hQ, averagedRowsFour_copy_sum rows hQ,
    fourCopyAllowance_copy_sum hQ, averagedFourComparison]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hd : D ≤ Q := by have := (Finset.mem_Icc.mp hD).2; omega
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, fockAverage_highestFour (by omega : 1 ≤ Q) hd]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) ε]
  simp only [fourComparison, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, smul_smul, ← sub_smul, ← add_smul]
  rw [fourSpinRatio_common_dimensions (by omega) hd]
  congr 1
  have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  have hm : (fourSpinDegree Q D+1 : ℂ) ≠ 0 := by
    rw [← Nat.cast_add_one]
    exact_mod_cast (show fourSpinDegree Q D+1 ≠ 0 by omega)
  simp only [Matrix.one_apply]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  split_ifs <;> field_simp

end LaughlinFock
end

end OAI
