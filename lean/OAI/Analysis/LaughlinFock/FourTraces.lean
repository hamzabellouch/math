import Mathlib
import OAI.Analysis.LaughlinFock.CopyVectors
import OAI.Analysis.LaughlinFock.ThreeTraces

namespace OAI

/-! Four Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

theorem composedCoupledVector_eq_sphericalCopy_all {Q D T r : ℕ}
    (hr : r ≤ D) (hD : D ≤ T) (hrQ : r ≤ Q) (hor : Odd r)
    (b : FourUncoupled Q) :
    composedCoupledVector Q r (D-r) (T-D) b =
      sphericalCopyCoefficient Q D T r b.1.val b.2.val.1.val b.2.val.2.val := by
  classical
  let p := b.1.val
  let j := b.2.val.1.val
  let k := b.2.val.2.val
  change (∑ a : Fin (2*Q-2*r+1),
    coupledVector (2*Q-2) (2*Q-2*r) (D-r) (T-D) p a.val *
    (Real.sqrt 2 * coupledVector Q Q r a.val j k)) =
      sphericalCopyCoefficient Q D T r p j k
  by_cases hjk : r ≤ j+k
  · by_cases ht : p+j+k=T
    · by_cases ha : j+k-r ≤ 2*Q-2*r
      · let a : Fin (2*Q-2*r+1) := ⟨j+k-r, by omega⟩
        rw [Finset.sum_eq_single a]
        · rw [sphericalCopyCoefficient, ite_eq_left ⟨hor, hr, hD, hjk, ht⟩]
          rw [coupledVector, ite_eq_left (show p+a.val = D-r+(T-D) by dsimp [a]; omega),
            coupledVector, ite_eq_left (show j+k = r+a.val by dsimp [a]; omega)]
          dsimp [a]
          ring
        · intro a' _ hne
          have he : j+k ≠ r+a'.val := by
            intro he
            apply hne
            apply Fin.ext
            dsimp [a]
            omega
          simp only [coupledVector, ite_eq_right he, mul_zero]
        · simp
      · have hc : coupledCoefficient Q Q r (j+k-r) j = 0 := by
          have h := congrFun (congrFun (coupledVector_outside_ladder
            (by omega : 2*r ≤ Q+Q) (by omega : Q+Q-2*r < j+k-r)) j) k
          dsimp only [coupledVector] at h
          rw [ite_eq_left (by omega : j+k = r+(j+k-r))] at h
          exact h
        rw [sphericalCopyCoefficient, ite_eq_left ⟨hor, hr, hD, hjk, ht⟩, hc, mul_zero, zero_mul]
        apply Finset.sum_eq_zero
        intro a _
        have hn : j+k ≠ r+a.val := by have := a.isLt; omega
        simp only [coupledVector, ite_eq_right hn, mul_zero]
    · rw [sphericalCopyCoefficient, ite_eq_right (by tauto)]
      apply Finset.sum_eq_zero
      intro a _
      by_cases he : j+k = r+a.val
      · have he' : p+a.val ≠ D-r+(T-D) := by omega
        simp only [coupledVector, ite_eq_right he', zero_mul]
      · simp only [coupledVector, ite_eq_right he, mul_zero]
  · rw [sphericalCopyCoefficient, ite_eq_right (by tauto)]
    apply Finset.sum_eq_zero
    intro a _
    have he : j+k ≠ r+a.val := by omega
    simp only [coupledVector, ite_eq_right he, mul_zero]

 

theorem sphericalCopyCoefficient_antisymm {Q r : ℕ} (hrQ : r ≤ Q)
    (D T p j k : ℕ) :
    sphericalCopyCoefficient Q D T r p k j = -sphericalCopyCoefficient Q D T r p j k := by
  by_cases h : Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ j+k ∧ p+j+k=T
  · have hs : Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ k+j ∧ p+k+j=T := by
      simpa only [Nat.add_comm k j, Nat.add_right_comm p k j] using h
    rw [sphericalCopyCoefficient, ite_eq_left hs, sphericalCopyCoefficient, ite_eq_left h,
      Nat.add_comm k j]
    have hc : coupledCoefficient Q Q r (j+k-r) k =
        -coupledCoefficient Q Q r (j+k-r) j := by
      have hv := coupledVector_antisymm hrQ h.1 (j+k-r) j k
      dsimp only [coupledVector] at hv
      rw [ite_eq_left (by omega : j+k=r+(j+k-r)),
        ite_eq_left (by omega : k+j=r+(j+k-r))] at hv
      exact hv
    rw [hc]
    ring
  · have hs : ¬ (Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ k+j ∧ p+k+j=T) := by
      simpa only [Nat.add_comm k j, Nat.add_right_comm p k j] using h
    simp only [sphericalCopyCoefficient, ite_eq_right h, ite_eq_right hs, neg_zero]

theorem sphericalCopyCoefficient_diagonal {Q r : ℕ} (hrQ : r ≤ Q)
    (D T p j : ℕ) : sphericalCopyCoefficient Q D T r p j j = 0 := by
  have h := sphericalCopyCoefficient_antisymm hrQ D T p j j
  linarith

 

def orderedFourColumn (Q : ℕ) (p : Fin (2*Q-2+1)) (j k : Orbital Q) : FourUncoupled Q → ℂ :=
  if h : j < k then Pi.single (p,⟨(j,k),h⟩) 1
  else if h : k < j then Pi.single (p,⟨(k,j),h⟩) (-1) else 0

 
theorem orderedFourColumn_wedgeAnnihilator (Q : ℕ) (p : Fin (2*Q-2+1)) (j k : Orbital Q) :
    wedgeAnnihilator Q 4 (wideFourWedgeMatrix Q *ᵥ orderedFourColumn Q p j k) =
      annihilator Q k * annihilator Q j * pairAnnihilator Q p.val := by
  classical
  rw [wedgeAnnihilator_mulVec]
  simp only [wideFourWedgeMatrix_annihilator_column]
  unfold orderedFourColumn
  split_ifs with h hk
  · simp [Pi.single_apply, ite_smul, apply_ite]
  · simp only [Pi.single_apply, apply_ite, star_neg, star_one, star_zero,
      ite_smul, neg_one_smul, zero_smul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [annihilator_swap Q j k, neg_mul, neg_neg]
  · have he : j=k := le_antisymm (le_of_not_gt hk) (le_of_not_gt h)
    subst k
    simp [annihilator_square]

 

theorem composed_orderedFourColumn_inner {Q D T r : ℕ}
    (hr : r ≤ D) (hD : D ≤ T) (hrQ : r ≤ Q) (hor : Odd r)
    (p : Fin (2*Q-2+1)) (j k : Orbital Q) :
    star (fun b => (composedCoupledVector Q r (D-r) (T-D) b : ℂ)) ⬝ᵥ
      orderedFourColumn Q p j k =
        (sphericalCopyCoefficient Q D T r p.val j.val k.val : ℂ) := by
  classical
  unfold orderedFourColumn
  split_ifs with h hk
  · rw [dotProduct_single]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, mul_one,
      composedCoupledVector_eq_sphericalCopy_all hr hD hrQ hor]
  · rw [dotProduct_single]
    change star (composedCoupledVector Q r (D-r) (T-D) (p,⟨(k,j),hk⟩) : ℂ) * (-1) = _
    rw [composedCoupledVector_eq_sphericalCopy_all hr hD hrQ hor]
    dsimp only
    rw [sphericalCopyCoefficient_antisymm hrQ D T p.val j.val k.val]
    simp
  · have he : j=k := le_antisymm (le_of_not_gt hk) (le_of_not_gt h)
    subst k
    simp [sphericalCopyCoefficient_diagonal hrQ]

 

def rowFourPrewedge {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → Fin (2*Q-2+1)) (i j : β → Orbital Q) (a : β → ℝ) :
    Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ :=
  -(∑ b, ∑ c, (a b*a c : ℂ) • Matrix.vecMulVec
    (orderedFourColumn Q (p b) (j b) (i c)) (star (orderedFourColumn Q (p c) (j c) (i b))))

 

theorem exteriorLift_outer_congruence {ι : Type*} [Fintype ι]
    (Q k : ℕ) (W : Matrix (SectorOccupation Q k) ι ℂ) (x y : ι → ℂ) :
    exteriorLift Q k (W * Matrix.vecMulVec x (star y) * Wᴴ) =
      (wedgeAnnihilator Q k (W *ᵥ x))ᴴ * wedgeAnnihilator Q k (W *ᵥ y) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, exteriorLift_rankOne]

 

theorem rowFourPrewedge_lift {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → Fin (2*Q-2+1)) (i j : β → Orbital Q) (a : β → ℝ) :
    exteriorLift Q 4 (wideFourWedgeMatrix Q * rowFourPrewedge Q p i j a *
      (wideFourWedgeMatrix Q)ᴴ) = rowFourBody Q (fun b => (p b).val) i j a := by
  classical
  have hs (c : ℂ) (M : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ) :
      exteriorLift Q 4 (c • M) = c • exteriorLift Q 4 M :=
    (exteriorLiftLinear Q 4).map_smul c M
  have hn (M : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ) :
      exteriorLift Q 4 (-M) = -exteriorLift Q 4 M := (exteriorLiftLinear Q 4).map_neg M
  simp only [rowFourPrewedge, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hn, exteriorLift_sum, hs,
    exteriorLift_outer_congruence, orderedFourColumn_wedgeAnnihilator]
  unfold rowFourBody
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ext A B
  simp [Matrix.smul_apply, Complex.real_smul, Matrix.mul_assoc]

 

theorem outer_bilinear {ι : Type*} [Fintype ι] (u v x y : ι → ℂ) :
    star x ⬝ᵥ (Matrix.vecMulVec u (star v) *ᵥ y) =
      (star x ⬝ᵥ u) * star (star y ⬝ᵥ v) := by
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul, Matrix.star_dotProduct v y]

 

theorem rowFourPrewedge_coupled_bilinear {β : Type*} [Fintype β]
    {Q D T r s : ℕ} (hr : r ≤ D) (hs : s ≤ D) (hD : D ≤ T)
    (hrQ : r ≤ Q) (hsQ : s ≤ Q) (hor : Odd r) (hos : Odd s)
    (p : β → Fin (2*Q-2+1)) (i j : β → Orbital Q) (a : β → ℝ) :
    star (fun b => (composedCoupledVector Q r (D-r) (T-D) b : ℂ)) ⬝ᵥ
      (rowFourPrewedge Q p i j a *ᵥ
        fun b => (composedCoupledVector Q s (D-s) (T-D) b : ℂ)) =
      (-(∑ b, ∑ c, a b*a c *
        sphericalCopyCoefficient Q D T r (p b).val (j b).val (i c).val *
        sphericalCopyCoefficient Q D T s (p c).val (j c).val (i b).val) : ℝ) := by
  classical
  simp only [rowFourPrewedge, Matrix.neg_mulVec, dotProduct_neg,
    Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    outer_bilinear, composed_orderedFourColumn_inner hr hD hrQ hor,
    composed_orderedFourColumn_inner hs hD hsQ hos, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul, mul_assoc]

 
def sourceRowFourP {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : Fin (2*Q-2+1) :=
  ⟨rowP b, by have := (rowEntry_bounds b).1; omega⟩

 
def sourceRowFourKernel {Q t : ℕ} (hQ : 8 ≤ Q) (a : RowEntry t → ℝ) :
    Matrix (FourUncoupled Q) (FourUncoupled Q) ℂ :=
  rowFourPrewedge Q (sourceRowFourP hQ) (sourceRowI hQ) (sourceRowJ hQ) a

theorem sourceRowFourKernel_lift {Q t : ℕ} (hQ : 8 ≤ Q) (a : RowEntry t → ℝ) :
    exteriorLift Q 4 (wideFourWedgeMatrix Q * sourceRowFourKernel hQ a *
      (wideFourWedgeMatrix Q)ᴴ) =
      rowFourBody Q rowP (sourceRowI hQ) (sourceRowJ hQ) a :=
  rowFourPrewedge_lift Q (sourceRowFourP hQ) (sourceRowI hQ) (sourceRowJ hQ) a

 

theorem sphericalCopyCoefficient_level (Q D T r p j k : ℕ) (h : p+j+k ≠ T) :
    sphericalCopyCoefficient Q D T r p j k = 0 := by
  simp [sphericalCopyCoefficient, h]

 

theorem rowFour_copyWeight_sum {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (r s : CopyLabel D) (b c : RowEntry t) :
    (∑ k : Fin (4*Q-1-2*D),
      sphericalCopyCoefficient Q D (D+k.val) r.val.val (rowP b) (rowJ b) (rowI c) *
      sphericalCopyCoefficient Q D (D+k.val) s.val.val (rowP c) (rowJ c) (rowI b)) =
      sphericalCopyCoefficient Q D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      sphericalCopyCoefficient Q D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b) := by
  classical
  have hl := rowFourLevel_le b c
  by_cases hd : D ≤ rowFourLevel b c
  · let k : Fin (4*Q-1-2*D) := ⟨rowFourLevel b c-D, by omega⟩
    rw [Finset.sum_eq_single k]
    · have he : D+k.val = rowFourLevel b c := by dsimp [k]; omega
      rw [he]
    · intro k' _ hne
      have he : rowP b+rowJ b+rowI c ≠ D+k'.val := by
        intro he
        apply hne
        apply Fin.ext
        dsimp [k]
        dsimp [rowFourLevel] at *
        omega
      rw [sphericalCopyCoefficient_level _ _ _ _ _ _ _ he, zero_mul]
    · simp
  · have hz : sphericalCopyCoefficient Q D (rowFourLevel b c) r.val.val
        (rowP b) (rowJ b) (rowI c) = 0 := by
      simp [sphericalCopyCoefficient, hd]
    rw [hz, zero_mul]
    apply Finset.sum_eq_zero
    intro k _
    have he : rowP b+rowJ b+rowI c ≠ D+k.val := by
      dsimp [rowFourLevel] at hd
      omega
    rw [sphericalCopyCoefficient_level _ _ _ _ _ _ _ he, zero_mul]

 

theorem sourceRowFourKernel_copyTrace {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    (∑ k : Fin (4*Q-1-2*D),
      star (fun b => (composedCoupledVector Q r.val.val (D-r.val.val) k.val b : ℂ)) ⬝ᵥ
        (sourceRowFourKernel (by omega : 8 ≤ Q) a *ᵥ
          fun b => (composedCoupledVector Q s.val.val (D-s.val.val) k.val b : ℂ))) =
      (rowFourTrace Q D t a r s : ℂ) := by
  classical
  have hr : r.val.val ≤ D := by have := r.val.isLt; omega
  have hs : s.val.val ≤ D := by have := s.val.isLt; omega
  have he (k : Fin (4*Q-1-2*D)) := rowFourPrewedge_coupled_bilinear
    hr hs (by omega : D ≤ D+k.val) (by omega : r.val.val ≤ Q)
    (by omega : s.val.val ≤ Q) r.property s.property
    (sourceRowFourP (by omega : 8 ≤ Q))
    (sourceRowI (by omega : 8 ≤ Q)) (sourceRowJ (by omega : 8 ≤ Q)) a
  simp only [Nat.add_sub_cancel_left, sourceRowFourP, sourceRowI, sourceRowJ] at he
  simp only [sourceRowFourKernel, he]
  rw [← Complex.ofReal_sum]
  apply congrArg (fun x : ℝ => (x : ℂ))
  simp only [rowFourTrace, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [rowFour_copyWeight_sum hQ hD]

end LaughlinFock
end

end OAI
