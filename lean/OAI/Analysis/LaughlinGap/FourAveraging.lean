import Mathlib
import OAI.Analysis.LaughlinGap.LowNested

namespace OAI

/-! Four Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

@[simp] lemma combination_single {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : ι → Matrix κ κ ℝ)
    (i : ι) : combination B (Pi.single i 1) = B i := by
  simp [combination, Pi.single_apply, ite_smul]

noncomputable def fourAnnihilator (Q D T r : ℕ) : FockMatrix (Q+1) :=
  combination (physicalFour Q) (nestedTensor (2*Q-2) Q Q r (D-r) (T-D))

lemma fourAnnihilator_even {Q D T r : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (hD : D ≤ T) (hr : r ≤ D) (he : Even r) : fourAnnihilator Q D T r = 0 := by
  exact physicalFour_even_null (by omega) he (by omega)

lemma fourAnnihilator_eq_embedding {Q D T r : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (hD : D ≤ T) (hr : r ≤ D) :
    fourAnnihilator Q D T r = combination (physicalFour Q)
      ((nestedAtDeficit (show r ≤ min Q Q by omega) hr
        (show D-r ≤ min (2*Q-2) (Q+Q-2*r) by omega)).toLinearMap
          (Pi.single (⟨T-D, by omega⟩ : Fin ((2*Q-2)+Q+Q-2*D+1)) 1)) := by
  rw [nestedAtDeficit_single]
  rfl

lemma fourAnnihilator_average {Q T U D E r s : ℕ} (hQ : 2 ≤ Q)
    (hT : T ≤ Q) (hU : U ≤ Q) (hD : D ≤ T) (hE : E ≤ U)
    (hr : r ≤ D) (hs : s ≤ E) :
    average (rotationCommutant (fockLowering Q))
      ((fourAnnihilator Q D T r).transpose * fourAnnihilator Q E U s) =
      if D=E ∧ T=U then average (rotationCommutant (fockLowering Q))
        ((fourAnnihilator Q D D r).transpose * fourAnnihilator Q E E s) else 0 := by
  classical
  by_cases hDE : D=E
  · subst E
    rw [fourAnnihilator_eq_embedding hQ hT hD hr,
      fourAnnihilator_eq_embedding hQ hU hE hs,
      (physicalFour_covariant hQ).equal_descendant_average,
      fourAnnihilator_eq_embedding hQ (by omega : D ≤ Q) le_rfl hr,
      fourAnnihilator_eq_embedding hQ (by omega : D ≤ Q) le_rfl hs]
    simp only [true_and, Nat.sub_self]
    congr 1
    apply propext
    simp only [Fin.mk.injEq]
    omega
  · rw [ite_eq_right (by tauto), fourAnnihilator_eq_embedding hQ hT hD hr,
      fourAnnihilator_eq_embedding hQ hU hE hs]
    exact (physicalFour_covariant hQ).distinct_descendant_average (by omega) _ _ _ _

lemma rawFour_expansion {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val=T) :
    annihilation a.2.2 * annihilation a.2.1 * physicalPair Q a.1.val =
      ∑ D : Fin (T+1), ∑ r : FourCopy D.val,
        fourBodyCoefficient Q D.val T r.val.val a.1.val a.2.1.val a.2.2.val •
          fourAnnihilator Q D.val T r.val.val := by
  classical
  have h := congrArg (combination (physicalFour Q)) (nestedTensor_low_expansion hQ hT a ha)
  simp only [map_sum, map_smul, combination_single] at h
  have h' := congrArg (fun M => Real.sqrt 2 • M) h
  have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hc (D : Fin (T+1)) (r : Fin (D.val+1)) := lowNested_coefficient
    (Nat.le_of_lt_succ r.isLt) (Nat.le_of_lt_succ D.isLt) hT a
  simp only [Fintype.sum_sigma, Finset.smul_sum, smul_smul, hc,
    physicalFour, productFamily] at h'
  rw [mul_one_div_cancel hn, one_smul] at h'
  change (∑ D : Fin (T+1), ∑ r : Fin (D.val+1),
    fourBodyCoefficient Q D.val T r.val a.1.val a.2.1.val a.2.2.val •
      fourAnnihilator Q D.val T r.val) = _ at h'
  rw [← h']
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin (D.val+1) => Odd r.val))
    (by simp) (fun r => fourBodyCoefficient Q D.val T r.val a.1.val a.2.1.val a.2.2.val •
      fourAnnihilator Q D.val T r.val)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases ho : Odd r.val
  · simp [ho]
  · have he : Even r.val := Nat.not_odd_iff_even.mp ho
    rw [ite_eq_right ho, fourAnnihilator_even hQ hT (Nat.le_of_lt_succ D.isLt)
      (Nat.le_of_lt_succ r.isLt) he, smul_zero]

lemma rawFour_cross_average {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a b : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val=T)
    (hb : b.1.val+b.2.1.val+b.2.2.val=T) :
    average (rotationCommutant (fockLowering Q))
      ((annihilation a.2.2 * annihilation a.2.1 * physicalPair Q a.1.val).transpose *
        (annihilation b.2.2 * annihilation b.2.1 * physicalPair Q b.1.val)) =
      ∑ D : Fin (T+1), ∑ r : FourCopy D.val, ∑ s : FourCopy D.val,
        (fourBodyCoefficient Q D.val T r.val.val a.1.val a.2.1.val a.2.2.val *
         fourBodyCoefficient Q D.val T s.val.val b.1.val b.2.1.val b.2.2.val) •
        average (rotationCommutant (fockLowering Q))
          ((fourAnnihilator Q D.val D.val r.val.val).transpose *
            fourAnnihilator Q D.val D.val s.val.val) := by
  classical
  rw [rawFour_expansion hQ hT a ha, rawFour_expansion hQ hT b hb]
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_sum, map_smul]
  conv_lhs =>
    arg 2; ext E
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext D
    arg 2; ext E
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext D
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro r hr
  have hblock (E : Fin (T+1)) (s : FourCopy E.val) :=
    fourAnnihilator_average hQ hT hT (Nat.le_of_lt_succ D.isLt)
      (Nat.le_of_lt_succ E.isLt) (Nat.le_of_lt_succ r.val.isLt) (Nat.le_of_lt_succ s.val.isLt)
  simp only [hblock, and_true, Fin.val_inj]
  rw [Finset.sum_eq_single D]
  · simp only [ite_true, mul_comm]
  · intro E hE hED
    apply Finset.sum_eq_zero
    intro s hs
    rw [ite_eq_right (Ne.symm hED), smul_zero]
  · simp

end LaughlinGap.RealOccupation

end

end OAI
