import OAI.Analysis.Laughlin.FourBody.CoefficientNorm
import OAI.Analysis.Laughlin.ThreeBody.RankTrace

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem physicalCouplingCoefficient_pair_swap (Q r j k : ℕ) (hr : r ≤ Q)
    (hor : Odd r) (hjk : j+k ≤ Q) :
    physicalCouplingCoefficient Q Q r (j+k) k = -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k
  · rw [physicalCouplingCoefficient,dite_eq_left ⟨h,by omega,hjk,hjk⟩,
      physicalCouplingCoefficient,dite_eq_left ⟨h,by omega,hjk,hjk⟩]
    have hp := pairCoupledTensor_antisymmetric Q r (j+k-r) hr hor ⟨j,by omega⟩ ⟨k,by omega⟩
    simpa only [pairCoupledTensor,Pi.smul_apply,smul_eq_mul,Nat.add_sub_cancel,Nat.add_sub_cancel_left] using hp
  · simp [physicalCouplingCoefficient,h]

theorem fourBodyCoefficient_swap (Q r D T p j k : ℕ) (hr : r ≤ Q) (hor : Odd r)
    (hjk : j+k ≤ Q) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  split_ifs
  · rw [physicalCouplingCoefficient_pair_swap Q r j k hr hor hjk]
    ring
  · simp

noncomputable def fourWedgeUnit (Q p j k : ℕ) : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ :=
  fun i => if i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k then 1 else 0

noncomputable def fourSignedUnit (Q p j k : ℕ) : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ :=
  fourWedgeUnit Q p j k - fourWedgeUnit Q p k j

theorem fourWedgeUnit_dot (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (hjk : j < k) (v : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ) :
    dotProduct v (fourWedgeUnit Q p j k) = v (⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
  classical
  simp only [dotProduct,fourWedgeUnit,mul_ite,mul_one,mul_zero]
  have he (i : Fin (2*Q-2+1) × WedgePairIndex Q) :
      (i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k) ↔
        i=(⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact Prod.ext (Fin.ext h1) (Subtype.ext (Prod.ext (Fin.ext h2) (Fin.ext h3)))
    · intro h; subst i; exact ⟨rfl,rfl,rfl⟩
  simp_rw [he]
  simp

theorem fourWedgeUnit_zero (Q p j k : ℕ) (hkj : k ≤ j) : fourWedgeUnit Q p j k=0 := by
  funext i
  have h := i.2.property
  simp only [fourWedgeUnit,Pi.zero_apply]
  rw [ite_eq_right (by rintro ⟨_,hj,hk⟩; change i.2.val.1.val < i.2.val.2.val at h; omega)]

theorem fourBodyCopy_signed_at_level (Q r D T p j k : ℕ) (hor : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQ : T+2 ≤ Q) (hT : p+j+k=T) :
    dotProduct (fourBodyCopy Q r D (by omega) (by omega)
      (by unfold genericCoupledWeight; omega) (T-D)) (fourSignedUnit Q p j k) =
      fourBodyCoefficient Q r D T p j k := by
  rw [fourSignedUnit,dotProduct_sub]
  rcases lt_trichotomy j k with h | h | h
  · rw [fourWedgeUnit_dot Q p j k (by omega) (by omega) (by omega) h,
      fourWedgeUnit_zero Q p k j (by omega),dotProduct_zero,sub_zero]
    exact fourBodyCopy_source_coefficient Q r D T hrD hDT hQ _ _ hT
  · subst k
    rw [sub_self]
    have he := fourBodyCoefficient_swap Q r D T p j j (by omega) hor (by omega)
    linarith
  · rw [fourWedgeUnit_zero Q p j k (by omega),dotProduct_zero,zero_sub,
      fourWedgeUnit_dot Q p k j (by omega) (by omega) (by omega) h,
      fourBodyCopy_source_coefficient Q r D T hrD hDT hQ _ _ (by dsimp; omega),
      fourBodyCoefficient_swap Q r D T p j k (by omega) hor (by omega),neg_neg]

theorem fourBodyCopy_signed_off (Q r D n p j k : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hT : p+j+k ≠ D+n) :
    dotProduct (fourBodyCopy Q r D hr hA hB n) (fourSignedUnit Q p j k) = 0 := by
  have hz (j k : ℕ) (hT : p+j+k ≠ D+n) :
      dotProduct (fourBodyCopy Q r D hr hA hB n) (fourWedgeUnit Q p j k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [fourWedgeUnit]
    split_ifs with he
    · rw [fourBodyCopy_off Q r D n hr hrD hA hB i.1 i.2 (by omega),zero_mul]
    · exact mul_zero _
  rw [fourSignedUnit,dotProduct_sub,hz j k hT,hz k j (by omega),sub_self]

end Laughlin.Spin

end OAI
