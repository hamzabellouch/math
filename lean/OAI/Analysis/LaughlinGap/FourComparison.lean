import Mathlib
import OAI.Analysis.LaughlinGap.AuxiliaryComparison
import OAI.Analysis.LaughlinGap.FourAveraging

namespace OAI

/-! Four Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def fourHighestAverage (Q D r s : ℕ) : FockMatrix (Q+1) :=
  average (rotationCommutant (fockLowering Q))
    ((fourAnnihilator Q D D r).transpose * fourAnnihilator Q D D s)

noncomputable def fourWeightCoefficient (Q D T r p j k : ℕ) : ℝ :=
  if D ≤ T then fourBodyCoefficient Q D T r p j k else 0

noncomputable def fourWeightCoefficientStar (D T r p j k : ℕ) : ℝ :=
  if D ≤ T then fourBodyCoefficientStar D T r p j k else 0

lemma fourWeightCoefficient_tendsto {D r : ℕ} (hr : r ≤ D) (T p j k : ℕ) :
    Tendsto (fun Q => fourWeightCoefficient Q D T r p j k) atTop
      (𝓝 (fourWeightCoefficientStar D T r p j k)) := by
  by_cases h : D ≤ T
  · simp only [fourWeightCoefficient,fourWeightCoefficientStar,ite_eq_left h]
    exact fourBodyCoefficient_tendsto hr h p j k
  · simp only [fourWeightCoefficient,fourWeightCoefficientStar,ite_eq_right h]
    exact tendsto_const_nhds

lemma rowFour_cross_average {Q : ℕ} (hQ : 23 ≤ Q) (r : RowData) (a b : RowEntry r.t) :
    average (rotationCommutant (fockLowering Q))
      ((annihilation ⟨b.output.val,by have := b.output.isLt; omega⟩ * rowTriple (by omega) a.val).transpose *
        (annihilation ⟨a.output.val,by have := a.output.isLt; omega⟩ * rowTriple (by omega) b.val)) =
      ∑ D : Fin 24, ∑ s : FourCopy D.val, ∑ t : FourCopy D.val,
        (fourWeightCoefficient Q D.val (a.val.1.val+a.val.2.val+b.output.val) s.val.val
            a.val.1.val a.val.2.val b.output.val *
         fourWeightCoefficient Q D.val (a.val.1.val+a.val.2.val+b.output.val) t.val.val
            b.val.1.val b.val.2.val a.output.val) •
          fourHighestAverage Q D.val s.val.val t.val.val := by
  let T := a.val.1.val+a.val.2.val+b.output.val
  have ht : T ≤ 23 := by have := a.val.1.isLt; have := a.val.2.isLt; have := b.output.isLt; omega
  let a' : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)) :=
    (⟨a.val.1.val,by have := a.val.1.isLt; omega⟩,
      (⟨a.val.2.val,by have := a.val.2.isLt; omega⟩,⟨b.output.val,by have := b.output.isLt; omega⟩))
  let b' : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)) :=
    (⟨b.val.1.val,by have := b.val.1.isLt; omega⟩,
      (⟨b.val.2.val,by have := b.val.2.isLt; omega⟩,⟨a.output.val,by have := a.output.isLt; omega⟩))
  have he : b'.1.val+b'.2.1.val+b'.2.2.val=T := by
    dsimp [b',T]; have := a.balance; have := b.balance; omega
  change average _ ((annihilation a'.2.2 * (annihilation a'.2.1 * physicalPair Q a'.1.val)).transpose *
    (annihilation b'.2.2 * (annihilation b'.2.1 * physicalPair Q b'.1.val))) = _
  rw [← Matrix.mul_assoc (annihilation a'.2.2), ← Matrix.mul_assoc (annihilation b'.2.2),
    rawFour_cross_average (by omega : 2 ≤ Q) (show T ≤ Q by omega) a' b' rfl he]
  change (∑ D : Fin (T+1), ∑ s : FourCopy D.val, ∑ t : FourCopy D.val,
    (fourBodyCoefficient Q D.val T s.val.val a.val.1.val a.val.2.val b.output.val *
      fourBodyCoefficient Q D.val T t.val.val b.val.1.val b.val.2.val a.output.val) •
        fourHighestAverage Q D.val s.val.val t.val.val) = _
  rw [sum_fin_extend ht (fun D => ∑ s : FourCopy D, ∑ t : FourCopy D,
    (fourBodyCoefficient Q D T s.val.val a.val.1.val a.val.2.val b.output.val *
      fourBodyCoefficient Q D T t.val.val b.val.1.val b.val.2.val a.output.val) •
        fourHighestAverage Q D s.val.val t.val.val)]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases h : D.val ≤ T <;> simp [fourWeightCoefficient,h,T]

noncomputable def rowFourMatrix
    (s : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (D : ℕ) (r : RowData) :
    Matrix (FourCopy D) (FourCopy D) ℝ := fun u v =>
  -(∑ a : RowEntry r.t, ∑ b : RowEntry r.t, r.alpha a*r.alpha b *
    s D (a.val.1.val+a.val.2.val+b.output.val) u.val.val a.val.1.val a.val.2.val b.output.val *
    s D (a.val.1.val+a.val.2.val+b.output.val) v.val.val b.val.1.val b.val.2.val a.output.val)

lemma rowFourMatrix_symmetric (s : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ)
    (D : ℕ) (r : RowData) : (rowFourMatrix s D r).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext u v
  simp only [rowFourMatrix,Matrix.transpose_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : b.val.1.val+b.val.2.val+a.output.val = a.val.1.val+a.val.2.val+b.output.val := by
    have := a.balance; have := b.balance; omega
  rw [he]
  ring

lemma rowFourMatrix_tendsto (D : ℕ) (r : RowData) (u v : FourCopy D) :
    Tendsto (fun Q => rowFourMatrix (fourWeightCoefficient Q) D r u v) atTop
      (𝓝 (rowFourMatrix fourWeightCoefficientStar D r u v)) := by
  unfold rowFourMatrix
  apply Tendsto.neg
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  exact ((fourWeightCoefficient_tendsto (Nat.le_of_lt_succ u.val.isLt) _ _ _ _).const_mul _).mul
    (fourWeightCoefficient_tendsto (Nat.le_of_lt_succ v.val.isLt) _ _ _ _)

lemma rowFour_average {Q : ℕ} (hQ : 23 ≤ Q) (r : RowData) :
    average (rotationCommutant (fockLowering Q)) (rowFour (by omega) r) =
      ∑ D : Fin 24, ∑ u : FourCopy D.val, ∑ v : FourCopy D.val,
        rowFourMatrix (fourWeightCoefficient Q) D.val r u v •
          fourHighestAverage Q D.val u.val.val v.val.val := by
  simp only [rowFour, map_neg, map_sum, map_smul, rowFour_cross_average hQ,
    Finset.smul_sum, smul_smul]
  conv_lhs =>
    arg 1; arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  conv_lhs =>
    arg 1; arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  conv_lhs =>
    arg 1; arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [← Finset.sum_smul, rowFourMatrix, neg_smul]
  congr 2
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

noncomputable def fourAverage (Q D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℝ →ₗ[ℝ] FockMatrix (Q+1) :=
  (average (rotationCommutant (fockLowering Q))).comp
    (lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val))

lemma fourAverage_eq (Q D : ℕ) (C : Matrix (FourCopy D) (FourCopy D) ℝ) :
    fourAverage Q D C = ∑ u, ∑ v, C u v • fourHighestAverage Q D u.val.val v.val.val := by
  simp only [fourAverage,LinearMap.comp_apply,lift,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    fourHighestAverage]

lemma rowFour_average_retained {Q : ℕ} (hQ : 23 ≤ Q) (r : RowData) :
    average (rotationCommutant (fockLowering Q)) (rowFour (by omega) r) =
      ∑ d : Fin 23, fourAverage Q (d.val+1)
        (rowFourMatrix (fourWeightCoefficient Q) (d.val+1) r) := by
  rw [rowFour_average hQ, Fin.sum_univ_succ]
  have hzero (u : FourCopy 0) : False := by have := u.property.pos; have := u.val.isLt; omega
  have hz : (∑ u : FourCopy 0, ∑ v : FourCopy 0,
    rowFourMatrix (fourWeightCoefficient Q) 0 r u v • fourHighestAverage Q 0 u.val.val v.val.val) = 0 :=
      Finset.sum_eq_zero (fun u _ => (hzero u).elim)
  simp only [Fin.val_zero,Fin.val_succ]
  rw [hz,zero_add]
  apply Finset.sum_congr rfl
  intro d hd
  exact (fourAverage_eq _ _ _).symm

noncomputable def fourCopyTarget (D : ℕ) : Matrix (FourCopy D) (FourCopy D) ℝ :=
  fun r s => if r.val.val=1 ∧ s.val.val=1 then 1 else 0

lemma fourCopyTarget_symmetric (D : ℕ) : (fourCopyTarget D).IsHermitian := by
  ext r s
  simp [fourCopyTarget,and_comm]

lemma fourAverage_copyTarget (Q : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    fourAverage Q D (fourCopyTarget D) = fourHighestAverage Q D 1 1 := by
  classical
  let r : FourCopy D := ⟨⟨1,by omega⟩,show Odd 1 by decide⟩
  have he (s : FourCopy D) : s.val.val=1 ↔ s=r := by
    constructor
    · intro hs; exact Subtype.ext (Fin.ext hs)
    · rintro rfl; rfl
  simp [fourAverage_eq,fourCopyTarget,he,ite_and,r]

end LaughlinGap.RealOccupation

end

end OAI
