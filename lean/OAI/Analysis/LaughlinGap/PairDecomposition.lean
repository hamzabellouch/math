import Mathlib
import OAI.Analysis.LaughlinGap.HighestRatios
import OAI.Analysis.LaughlinGap.IntertwiningSpin
import OAI.Analysis.LaughlinGap.NormalOrder
import OAI.Analysis.LaughlinGap.PairSpin

namespace OAI

/-! Pair Decomposition. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

noncomputable def tensorSwap (Q : ℕ) : LadderMap (tensorSpin Q Q) (tensorSpin Q Q) where
  toLinearMap := {
    toFun := fun x ij => x (ij.2,ij.1)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  lower x := by
    funext ⟨i,j⟩
    change lowering Q (fun i => x (j,i)) i + lowering Q (fun j => x (j,i)) j =
      lowering Q (fun j => x (j,i)) j + lowering Q (fun i => x (j,i)) i
    ring
  raise x := by
    funext ⟨i,j⟩
    change raising Q (fun i => x (j,i)) i + raising Q (fun j => x (j,i)) j =
      raising Q (fun j => x (j,i)) j + raising Q (fun i => x (j,i)) i
    ring

lemma highestCoefficient_last_equal_spin {Q r : ℕ} (hr : r ≤ Q) :
    highestCoefficient Q Q r r = (-1 : ℝ)^r * highestCoefficient Q Q r 0 := by
  have hf : (Q.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hr).ne'
  rw [highestCoefficient_last (by simpa using hr), div_self hf, Real.sqrt_one, mul_one,
    mul_comm]

theorem coupledTensor_swap {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (i j : Fin (Q+1)) :
    coupledTensor Q Q r l (j,i) = (-1 : ℝ)^r * coupledTensor Q Q r l (i,j) := by
  have h0 := tensorSpin_schur (by simpa using hr : r ≤ min Q Q)
    (Nat.zero_le _) (tensorSwap Q)
  let r' : Fin (Q+1) := ⟨r, by omega⟩
  have hc := congrFun h0 (0,r')
  simp only [coupledTensor_zero, tensorSwap, highestTensor, LinearMap.coe_mk,
    AddHom.coe_mk, Fin.val_zero, r', zero_add, add_zero, ite_true, Pi.smul_apply,
    smul_eq_mul] at hc
  have hb : dotProduct (highestTensor Q Q r)
      ((tensorSwap Q).toLinearMap (highestTensor Q Q r)) = (-1 : ℝ)^r := by
    apply mul_right_cancel₀ (highestCoefficient_zero_ne (by simpa using hr : r ≤ min Q Q))
    exact hc.symm.trans (highestCoefficient_last_equal_spin hr)
  have h := congrFun (tensorSpin_schur (by simpa using hr : r ≤ min Q Q) hl
    (tensorSwap Q)) (i,j)
  rw [hb] at h
  exact h

noncomputable def orbitalPairCoefficient (Q r l : ℕ) (a : PairLabel (Q+1)) : ℝ :=
  Real.sqrt 2 * coupledTensor Q Q r l (a.val.1,a.val.2)

lemma coupledTensor_antisymmetric {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (hodd : Odd r) (i j : Fin (Q+1)) :
    coupledTensor Q Q r l (j,i) = -coupledTensor Q Q r l (i,j) := by
  rw [coupledTensor_swap hr hl, hodd.neg_one_pow, neg_one_mul]

lemma coupledTensor_diag_zero {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (hodd : Odd r) (i : Fin (Q+1)) : coupledTensor Q Q r l (i,i) = 0 := by
  have h := coupledTensor_antisymmetric hr hl hodd i i
  linarith

lemma orbitalPair_inner {Q r s l k : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hl : l ≤ Q+Q-2*r) (hk : k ≤ Q+Q-2*s) (hro : Odd r) (hso : Odd s) :
    (∑ a : PairLabel (Q+1), orbitalPairCoefficient Q r l a * orbitalPairCoefficient Q s k a) =
      dotProduct (coupledTensor Q Q r l) (coupledTensor Q Q s k) := by
  have hsum := sum_increasing_pairs
    (fun i j : Fin (Q+1) => coupledTensor Q Q r l (i,j) * coupledTensor Q Q s k (i,j))
    (by intro i j; rw [coupledTensor_antisymmetric hr hl hro j i,
      coupledTensor_antisymmetric hs hk hso j i]; ring)
    (by intro i; rw [coupledTensor_diag_zero hr hl hro i, zero_mul])
  have he (a : PairLabel (Q+1)) :
      orbitalPairCoefficient Q r l a * orbitalPairCoefficient Q s k a =
      2 * (coupledTensor Q Q r l (a.val.1,a.val.2) *
        coupledTensor Q Q s k (a.val.1,a.val.2)) := by
    unfold orbitalPairCoefficient
    linear_combination (coupledTensor Q Q r l (a.val.1,a.val.2) *
      coupledTensor Q Q s k (a.val.1,a.val.2)) *
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simp only [he, ← Finset.mul_sum]
  rw [hsum]
  simp only [dotProduct, Fintype.sum_prod_type]

theorem orbitalPair_orthonormal {Q r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s)
    (l : Fin (Q+Q-2*r+1)) (k : Fin (Q+Q-2*s+1)) :
    (∑ a : PairLabel (Q+1), orbitalPairCoefficient Q r l.val a *
      orbitalPairCoefficient Q s k.val a) = if r=s ∧ l.val=k.val then 1 else 0 := by
  rw [orbitalPair_inner hr hs (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt) hro hso]
  by_cases hrs : r=s
  · subst s
    by_cases hlk : l.val=k.val
    · have : l=k := Fin.ext hlk
      subst k
      simp only [and_self, ite_true]
      exact coupledTensor_norm_sq (by simpa using hr) (Nat.le_of_lt_succ l.isLt)
    · rw [ite_eq_right (by simpa using hlk)]
      exact coupledTensor_orthogonal_same_spin (by simpa using hr)
        (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt) hlk
  · rw [ite_eq_right (by simp [hrs])]
    exact coupledTensor_orthogonal_distinct_spin (by simpa using hr) (by simpa using hs)
      (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt) hrs

theorem orbitalPairCoefficient_one {Q : ℕ} (hQ : 2 ≤ Q) (l : Fin (2*Q-2+1))
    (a : PairLabel (Q+1)) :
    orbitalPairCoefficient Q 1 l.val a =
      sphericalExteriorPairCoefficient Q l.val a.val.1 a.val.2 := by
  unfold orbitalPairCoefficient
  rw [← physicalPairTensor_eq_coupled hQ (Nat.le_of_lt_succ l.isLt)]
  exact (sphericalExteriorPairCoefficient_eq_tensor Q l.val a.val.1 a.val.2).symm

end LaughlinGap.Spin

end

end OAI
