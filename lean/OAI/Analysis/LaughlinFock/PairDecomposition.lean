import Mathlib
import OAI.Analysis.LaughlinFock.HighestTails

namespace OAI

/-! Pair Decomposition. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

def fourCouplingMatrix (Q : ℕ) :
    Matrix (PairLabel Q × PairLabel Q) (CoupledIndex (2*Q-2) (2*Q-2)) ℂ :=
  fun pq c => coupledVector (2*Q-2) (2*Q-2) c.1.val c.2.val pq.1.val pq.2.val

 
theorem fourCouplingMatrix_complete (Q : ℕ) (hQ : 1 ≤ Q) :
    fourCouplingMatrix Q * (fourCouplingMatrix Q)ᴴ = 1 := by
  classical
  ext pq rs
  have hdim : 2*Q-1 = 2*Q-2+1 := by omega
  let x : Fin (2*Q-2+1) × Fin (2*Q-2+1) :=
    (Fin.cast hdim pq.1, Fin.cast hdim pq.2)
  let y : Fin (2*Q-2+1) × Fin (2*Q-2+1) :=
    (Fin.cast hdim rs.1, Fin.cast hdim rs.2)
  have h := congrArg (fun t : ℝ => (t : ℂ))
    (coupledVector_resolution (2*Q-2) (2*Q-2) x y)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    fourCouplingMatrix, Complex.star_def, Complex.conj_ofReal,
    Matrix.one_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    x, y, Fin.val_cast, Prod.mk.injEq, Fin.cast_inj, ← Prod.ext_iff,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h

 
theorem fourCouplingMatrix_gram (Q : ℕ) (hQ : 1 ≤ Q) :
    (fourCouplingMatrix Q)ᴴ * fourCouplingMatrix Q = 1 := by
  classical
  ext c d
  have hc := coupledIndex_bounds c
  have hd := coupledIndex_bounds d
  have h := coupledVector_gram hc.1 hc.2.1 hd.1 hd.2.1 hc.2.2 hd.2.2
  rw [gridInner_eq_fin_sum] at h
  rw [show 2*Q-2+1 = 2*Q-1 by omega] at h
  have he : (c.1.val=d.1.val ∧ c.2.val=d.2.val) ↔ c=d := by
    constructor
    · intro ⟨hz,hk⟩
      rcases c with ⟨z,k⟩
      rcases d with ⟨r,l⟩
      have hr : z=r := Fin.ext hz
      subst r
      have hl : k=l := Fin.ext hk
      subst l
      rfl
    · rintro rfl
      exact ⟨rfl,rfl⟩
  simp only [he] at h
  have h' := congrArg (fun t : ℝ => (t : ℂ)) h
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    fourCouplingMatrix, Complex.star_def, Complex.conj_ofReal,
    Fintype.sum_prod_type, Matrix.one_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h'

 

def fourCoupledWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 4) (CoupledIndex (2*Q-2) (2*Q-2)) ℂ :=
  fourWedgeMatrix Q * fourCouplingMatrix Q

 
theorem fourCoupledWedgeMatrix_target (Q : ℕ) (hQ : 1 ≤ Q) :
    fourCoupledWedgeMatrix Q * (fourCoupledWedgeMatrix Q)ᴴ =
      fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ := by
  unfold fourCoupledWedgeMatrix
  rw [Matrix.conjTranspose_mul]
  calc
    _ = fourWedgeMatrix Q * (fourCouplingMatrix Q * (fourCouplingMatrix Q)ᴴ) *
        (fourWedgeMatrix Q)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [fourCouplingMatrix_complete Q hQ, Matrix.mul_one]

 

def retainedFourTarget (Q L : ℕ) : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ :=
  fourCoupledWedgeMatrix Q * Matrix.diagonal
    (fun c : CoupledIndex (2*Q-2) (2*Q-2) => if c.1.val+1 ≤ L then (1 : ℂ) else 0) *
      (fourCoupledWedgeMatrix Q)ᴴ

theorem retainedFourTarget_posSemidef (Q L : ℕ) :
    (retainedFourTarget Q L).PosSemidef := by
  classical
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro c
  split_ifs <;> norm_num

 

theorem discardedFourTarget_posSemidef (Q L : ℕ) (hQ : 1 ≤ Q) :
    (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ - retainedFourTarget Q L).PosSemidef := by
  classical
  rw [← fourCoupledWedgeMatrix_target Q hQ]
  have hd : (1 - Matrix.diagonal
      (fun c : CoupledIndex (2*Q-2) (2*Q-2) => if c.1.val+1 ≤ L then (1 : ℂ) else 0)).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro c
    split_ifs <;> norm_num
  convert hd.mul_mul_conjTranspose_same (fourCoupledWedgeMatrix Q) using 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, retainedFourTarget]

 

theorem discardedFourTarget_lift_posSemidef (Q L : ℕ) (hQ : 1 ≤ Q) :
    (exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) -
      exteriorLift Q 4 (retainedFourTarget Q L)).PosSemidef := by
  rw [← exteriorLift_sub]
  exact exteriorLift_posSemidef Q 4 _ (discardedFourTarget_posSemidef Q L hQ)

 
theorem fourWedgeMatrix_swap (Q : ℕ) (A : SectorOccupation Q 4)
    (p q : PairLabel Q) : fourWedgeMatrix Q A (q,p) = fourWedgeMatrix Q A (p,q) := by
  unfold fourWedgeMatrix
  rw [pairAnnihilators_commute Q p.val q.val]

 
def fourCoupledAnnihilator (Q z k : ℕ) : FockMatrix Q :=
  ∑ p : PairLabel Q, ∑ q : PairLabel Q,
    (coupledVector (2*Q-2) (2*Q-2) z k p.val q.val : ℂ) •
      (pairAnnihilator Q q.val * pairAnnihilator Q p.val)

 

theorem fourCoupledAnnihilator_odd_zero {Q z : ℕ} (hz : z ≤ 2*Q-2)
    (ho : Odd z) (k : ℕ) : fourCoupledAnnihilator Q z k = 0 := by
  have h : fourCoupledAnnihilator Q z k = -fourCoupledAnnihilator Q z k := by
    unfold fourCoupledAnnihilator
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [coupledVector_antisymm hz ho k p.val q.val,
      pairAnnihilators_commute Q p.val q.val, Complex.ofReal_neg, neg_smul, neg_neg]
  have h' := eq_neg_iff_add_eq_zero.mp h
  have he : (2 : ℂ) • fourCoupledAnnihilator Q z k = 0 := by simpa only [two_smul] using h'
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

 
theorem fourWedgeMatrix_annihilator_column (Q : ℕ) (pq : PairLabel Q × PairLabel Q) :
    wedgeAnnihilator Q 4 (fun A => fourWedgeMatrix Q A pq) =
      pairAnnihilator Q pq.2.val * pairAnnihilator Q pq.1.val := by
  apply wedgeAnnihilator_annihilatorVector
  exact annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q pq.1.val)
    (pairAnnihilator_mem Q pq.2.val)

 

theorem fourCoupledAnnihilator_eq_wedge (Q : ℕ)
    (c : CoupledIndex (2*Q-2) (2*Q-2)) :
    fourCoupledAnnihilator Q c.1.val c.2.val =
      wedgeAnnihilator Q 4 (fun A => fourCoupledWedgeMatrix Q A c) := by
  change _ = wedgeAnnihilator Q 4
    (fourWedgeMatrix Q *ᵥ fun pq => fourCouplingMatrix Q pq c)
  rw [wedgeAnnihilator_mulVec]
  simp only [fourWedgeMatrix_annihilator_column, fourCouplingMatrix,
    Complex.star_def, Complex.conj_ofReal, Fintype.sum_prod_type, fourCoupledAnnihilator]

 

theorem retainedFourTarget_lift (Q L : ℕ) :
    exteriorLift Q 4 (retainedFourTarget Q L) =
      ∑ c : CoupledIndex (2*Q-2) (2*Q-2), if c.1.val+1 ≤ L then
        (fourCoupledAnnihilator Q c.1.val c.2.val)ᴴ *
          fourCoupledAnnihilator Q c.1.val c.2.val else 0 := by
  classical
  unfold retainedFourTarget
  rw [exteriorLift_congruence]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Matrix.diagonal_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ c)]
  rw [← fourCoupledAnnihilator_eq_wedge]
  split_ifs <;> simp

end LaughlinFock
end

end OAI
