import Mathlib
import OAI.Analysis.LaughlinGap.PhysicalAveraging
import OAI.Analysis.LaughlinGap.ThreeAveraging

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

abbrev RowEntry (t : Fin 8) :=
  {a : Fin 8 × Fin 9 // t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8}

def RowEntry.output {t : Fin 8} (a : RowEntry t) : Fin 9 :=
  ⟨a.val.1.val+a.val.2.val-t.val,by have := a.property; omega⟩

lemma RowEntry.balance {t : Fin 8} (a : RowEntry t) :
    t.val+a.output.val = a.val.1.val+a.val.2.val := by
  dsimp [RowEntry.output]; have := a.property; omega

structure RowData where
  t : Fin 8
  lam : ℝ
  alpha : RowEntry t → ℝ

noncomputable def rowTriple {Q : ℕ} (hQ : 8 ≤ Q) (a : Fin 8 × Fin 9) :
    FockMatrix (Q+1) :=
  annihilation ⟨a.2.val,by omega⟩ * physicalPair Q a.1.val

noncomputable def rowAnnihilator {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) : FockMatrix (Q+1) :=
  r.lam • physicalPair Q r.t.val + ∑ a : RowEntry r.t,
    r.alpha a • (creation ⟨a.output.val,by have := a.output.isLt; omega⟩ * rowTriple hQ a.val)

noncomputable def rowThree {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) : FockMatrix (Q+1) :=
  (∑ a : RowEntry r.t, (r.lam*r.alpha a) •
    ((rowTriple hQ (r.t,a.output)).transpose * rowTriple hQ a.val +
      (rowTriple hQ a.val).transpose * rowTriple hQ (r.t,a.output))) +
  ∑ a : RowEntry r.t, ∑ b : RowEntry r.t, (r.alpha a*r.alpha b) •
    (if a.output=b.output then (rowTriple hQ a.val).transpose * rowTriple hQ b.val else 0)

noncomputable def rowFour {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) : FockMatrix (Q+1) :=
  -(∑ a : RowEntry r.t, ∑ b : RowEntry r.t, (r.alpha a*r.alpha b) •
    ((annihilation ⟨b.output.val,by have := b.output.isLt; omega⟩ * rowTriple hQ a.val).transpose *
      (annihilation ⟨a.output.val,by have := a.output.isLt; omega⟩ * rowTriple hQ b.val)))

lemma rowSquare_split {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) :
    (rowAnnihilator hQ r).transpose * rowAnnihilator hQ r =
      (r.lam^2) • ((physicalPair Q r.t.val).transpose * physicalPair Q r.t.val) +
      rowThree hQ r + rowFour hQ r := by
  classical
  apply complexify_injective
  let i : RowEntry r.t → Fin (Q+1) := fun a => ⟨a.output.val,by have := a.output.isLt; omega⟩
  have hi (a b : RowEntry r.t) : i a=i b ↔ a.output=b.output := by
    simp only [i,Fin.ext_iff]
  have h := Occupation.auxiliaryRow_square r.lam
    (complexify (physicalPair Q r.t.val)) r.alpha i
    (fun a => complexify (rowTriple hQ a.val))
  have ha : complexify (rowAnnihilator hQ r) =
      Occupation.auxiliaryRow r.lam (complexify (physicalPair Q r.t.val)) r.alpha i
        (fun a => complexify (rowTriple hQ a.val)) := by
    simp only [rowAnnihilator, map_add, map_sum, map_smul, map_mul, complexify_creation,
      Occupation.auxiliaryRow, i]
    rfl
  simp only [map_add, map_smul, map_mul, complexify_transpose, ha]
  rw [h]
  simp only [rowThree,rowFour,map_add,map_sum,map_smul,map_neg,map_mul,
    complexify_transpose, apply_ite, map_zero, hi, rowTriple, complexify_annihilation]
  simp only [i,sub_eq_add_neg,add_assoc]
  rfl

lemma rowSquare_average {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) :
    ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
       ((rowAnnihilator hQ r).transpose * rowAnnihilator hQ r) =
      r.lam^2 • physicalHamiltonian Q +
      ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (rowThree hQ r) +
      ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (rowFour hQ r) := by
  rw [rowSquare_split, map_add, map_add, map_smul,
    physicalPair_single_val (by omega) (by have := r.t.isLt; omega)]
  have hn : ((2*Q-1:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [smul_add, smul_smul]
  congr 2
  field_simp

noncomputable def threeWeightCoefficient (Q z T p : ℕ) : ℝ :=
  if z ≤ T then coupledCoefficient (2*Q-2) Q z (T-z) p else 0

noncomputable def threeHighestAverage (Q z : ℕ) : FockMatrix (Q+1) :=
  average (rotationCommutant (fockLowering Q))
    ((combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)).transpose *
      combination (physicalTriple Q) (highestTensor (2*Q-2) Q z))

lemma sum_fin_extend {M : Type*} [AddCommMonoid M] {T K : ℕ} (h : T ≤ K) (f : ℕ → M) :
    (∑ z : Fin (T+1), f z.val) = ∑ z : Fin (K+1), if z.val ≤ T then f z.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range f,
    Fin.sum_univ_eq_sum_range (fun z => if z ≤ T then f z else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_range,Finset.mem_filter]
  omega

lemma rowTriple_cross_average {Q T : ℕ} (hQ : 15 ≤ Q)
    (a b : Fin 8 × Fin 9) (ha : a.1.val+a.2.val=T) (hb : b.1.val+b.2.val=T) :
    average (rotationCommutant (fockLowering Q))
      ((rowTriple (by omega) a).transpose * rowTriple (by omega) b) =
      ∑ z : Fin 16,
        (threeWeightCoefficient Q z.val T a.1.val * threeWeightCoefficient Q z.val T b.1.val) •
          threeHighestAverage Q z.val := by
  have ht : T ≤ 15 := by have := a.1.isLt; have := a.2.isLt; omega
  let a' : Fin (2*Q-2+1) × Fin (Q+1) := (⟨a.1.val,by omega⟩,⟨a.2.val,by omega⟩)
  let b' : Fin (2*Q-2+1) × Fin (Q+1) := (⟨b.1.val,by omega⟩,⟨b.2.val,by omega⟩)
  change average _ ((physicalTriple Q a').transpose * physicalTriple Q b') = _
  rw [(physicalTriple_covariant (by omega : 2 ≤ Q)).rawTensor_cross_average (by omega) a' b' ha hb]
  change (∑ z : Fin (T+1),
    (coupledCoefficient (2*Q-2) Q z.val (T-z.val) a.1.val * coupledCoefficient (2*Q-2) Q z.val (T-z.val) b.1.val) •
      threeHighestAverage Q z.val) = _
  rw [sum_fin_extend ht (fun z =>
    (coupledCoefficient (2*Q-2) Q z (T-z) a.1.val *
      coupledCoefficient (2*Q-2) Q z (T-z) b.1.val) • threeHighestAverage Q z)]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp [a',b']
  by_cases hzt : z.val ≤ T <;> simp [threeWeightCoefficient,hzt,threeHighestAverage]

noncomputable def rowTrace (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ) (r : RowData) : ℝ :=
  (∑ a : RowEntry r.t, 2*r.lam*r.alpha a *
    s z (r.t.val+a.output.val) r.t.val *
    s z (r.t.val+a.output.val) a.val.1.val) +
  ∑ a : RowEntry r.t, ∑ b : RowEntry r.t,
    if a.output=b.output then r.alpha a*r.alpha b *
      s z (r.t.val+a.output.val) a.val.1.val *
      s z (r.t.val+a.output.val) b.val.1.val else 0

noncomputable def rowThreeTrace (Q z : ℕ) (r : RowData) : ℝ :=
  rowTrace (threeWeightCoefficient Q) z r

lemma rowThree_average {Q : ℕ} (hQ : 15 ≤ Q) (r : RowData) :
    average (rotationCommutant (fockLowering Q)) (rowThree (by omega) r) =
      ∑ z : Fin 16, rowThreeTrace Q z.val r • threeHighestAverage Q z.val := by
  classical
  have ha (a : RowEntry r.t) := rowTriple_cross_average hQ (r.t,a.output) a.val rfl a.balance.symm
  have hb (a : RowEntry r.t) := rowTriple_cross_average hQ a.val (r.t,a.output) a.balance.symm rfl
  have hc (a b : RowEntry r.t) :
      average (rotationCommutant (fockLowering Q))
        (if a.output=b.output then (rowTriple (by omega) a.val).transpose * rowTriple (by omega) b.val else 0) =
      ∑ z : Fin 16, (if a.output=b.output then
        threeWeightCoefficient Q z.val (r.t.val+a.output.val) a.val.1.val *
        threeWeightCoefficient Q z.val (r.t.val+a.output.val) b.val.1.val else 0) •
          threeHighestAverage Q z.val := by
    by_cases hab : a.output=b.output
    · rw [ite_eq_left hab,rowTriple_cross_average hQ a.val b.val a.balance.symm (by rw [hab];exact b.balance.symm)]
      simp only [hab,ite_true]
    · simp [hab]
  have hd (a : RowEntry r.t) :
      average (rotationCommutant (fockLowering Q))
        ((rowTriple (by omega) (r.t,a.output)).transpose * rowTriple (by omega) a.val +
          (rowTriple (by omega) a.val).transpose * rowTriple (by omega) (r.t,a.output)) =
      ∑ z : Fin 16, (2 * threeWeightCoefficient Q z.val (r.t.val+a.output.val) r.t.val *
        threeWeightCoefficient Q z.val (r.t.val+a.output.val) a.val.1.val) •
          threeHighestAverage Q z.val := by
    rw [map_add,ha,hb,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    rw [← add_smul]
    congr 1
    ring
  rw [rowThree,map_add]
  simp only [map_sum,map_smul,hd,hc,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm (f := fun (a : RowEntry r.t) (z : Fin 16) => _)]
  conv_lhs =>
    arg 2; arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun (a : RowEntry r.t) (z : Fin 16) => _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [← Finset.sum_smul, ← add_smul, rowThreeTrace, rowTrace]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> ring

end LaughlinGap.RealOccupation

end

end OAI
