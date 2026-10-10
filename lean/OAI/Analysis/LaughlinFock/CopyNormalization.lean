import Mathlib
import OAI.Analysis.LaughlinFock.NormalOrdering
import OAI.Analysis.LaughlinFock.TensorBasis

namespace OAI

/-! Copy Normalization. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

theorem antisymmetric_wedge_inner (Q : ℕ) (f g : Orbital Q → Orbital Q → ℝ)
    (hf : ∀ i j, f j i = -f i j) (hg : ∀ i j, g j i = -g i j) :
    (∑ ij : IncreasingPair Q,
      (Real.sqrt 2 * f ij.val.1 ij.val.2) * (Real.sqrt 2 * g ij.val.1 ij.val.2)) =
      ∑ i : Orbital Q, ∑ j : Orbital Q, f i j * g i j := by
  have hdiag (i : Orbital Q) : f i i = 0 := by have h := hf i i; linarith
  have hterm (i j : Orbital Q) : f i j * g i j =
      (if i < j then f i j * g i j else 0) + (if j < i then f j i * g j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), zero_add, hf i j, hg i j, neg_mul_neg]
  have hsum : (∑ i : Orbital Q, ∑ j : Orbital Q, f i j * g i j) =
      2 * ∑ i : Orbital Q, ∑ j : Orbital Q, if i < j then f i j * g i j else 0 := by
    calc
      _ = ∑ i : Orbital Q, ∑ j : Orbital Q,
          ((if i < j then f i j * g i j else 0) + (if j < i then f j i * g j i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hterm i j
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : Orbital Q => if j < i then f j i * g j i else 0)]
        ring
  rw [increasingPair_sum Q (fun i j => (Real.sqrt 2 * f i j) * (Real.sqrt 2 * g i j)), hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · calc
      _ = (Real.sqrt 2)^2 * (f i j * g i j) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · simp

 

def wedgeCoupledCoefficient (Q r k : ℕ) (ij : IncreasingPair Q) : ℝ :=
  Real.sqrt 2 * coupledVector Q Q r k ij.val.1.val ij.val.2.val

theorem gridInner_eq_fin_sum (n m : ℕ) (f g : GridVector) :
    gridInner n m f g = ∑ p : Fin (n+1), ∑ q : Fin (m+1), f p.val q.val * g p.val q.val := by
  symm
  calc
    _ = ∑ p : Fin (n+1), ∑ q ∈ Finset.range (m+1), f p.val q * g p.val q := by
      apply Finset.sum_congr rfl
      intro p _
      exact Fin.sum_univ_eq_sum_range (fun q => f p.val q * g p.val q) (m+1)
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun p => ∑ q ∈ Finset.range (m+1), f p q * g p q) (n+1)

 

theorem wedgeCoupledCoefficient_gram {Q r s k l : ℕ}
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s)
    (hk : k ≤ 2*Q-2*r) (hl : l ≤ 2*Q-2*s) :
    (∑ ij : IncreasingPair Q, wedgeCoupledCoefficient Q r k ij *
      wedgeCoupledCoefficient Q s l ij) = if r=s ∧ k=l then 1 else 0 := by
  unfold wedgeCoupledCoefficient
  rw [antisymmetric_wedge_inner Q
    (fun i j => coupledVector Q Q r k i.val j.val)
    (fun i j => coupledVector Q Q s l i.val j.val)
    (fun i j => coupledVector_antisymm hr hor k i.val j.val)
    (fun i j => coupledVector_antisymm hs hos l i.val j.val)]
  rw [← gridInner_eq_fin_sum]
  exact coupledVector_gram hr hr hs hs (by omega) (by omega)

 

theorem tensor_contraction_inner {P I A B : Type*}
    [Fintype P] [Fintype I] [Fintype A] [Fintype B]
    (x : P → A → ℝ) (y : P → B → ℝ) (u : A → I → ℝ) (v : B → I → ℝ) :
    (∑ p, ∑ i, (∑ a, x p a * u a i) * (∑ b, y p b * v b i)) =
      ∑ p, ∑ a, ∑ b, (x p a * y p b) * (∑ i, u a i * v b i) := by
  apply Finset.sum_congr rfl
  intro p _
  have ht (i : I) : (∑ a, x p a * u a i) * (∑ b, y p b * v b i) =
      ∑ a, ∑ b, (x p a * u a i) * (y p b * v b i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  simp only [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

 

def composedCoupledVector (Q r z k : ℕ)
    (b : Fin (2*Q-2+1) × IncreasingPair Q) : ℝ :=
  ∑ a : Fin (2*Q-2*r+1),
    coupledVector (2*Q-2) (2*Q-2*r) z k b.1.val a.val *
      wedgeCoupledCoefficient Q r a.val b.2

 

theorem composedCoupledVector_gram {Q r s z w k l : ℕ}
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s)
    (hz₁ : z ≤ 2*Q-2) (hz₂ : z ≤ 2*Q-2*r)
    (hw₁ : w ≤ 2*Q-2) (hw₂ : w ≤ 2*Q-2*s)
    (hk : k ≤ (2*Q-2)+(2*Q-2*r)-2*z)
    (hl : l ≤ (2*Q-2)+(2*Q-2*s)-2*w) :
    (∑ b : Fin (2*Q-2+1) × IncreasingPair Q,
      composedCoupledVector Q r z k b * composedCoupledVector Q s w l b) =
        if r=s ∧ z=w ∧ k=l then 1 else 0 := by
  classical
  simp only [Fintype.sum_prod_type, composedCoupledVector]
  rw [tensor_contraction_inner]
  simp_rw [wedgeCoupledCoefficient_gram hr hs hor hos
    (Nat.le_of_lt_succ (Fin.isLt _)) (Nat.le_of_lt_succ (Fin.isLt _))]
  by_cases hrs : r=s
  · subst s
    have hsimp (p : Fin (2*Q-2+1)) (a : Fin (2*Q-2*r+1)) :
        (∑ b : Fin (2*Q-2*r+1),
          (coupledVector (2*Q-2) (2*Q-2*r) z k p.val a.val *
           coupledVector (2*Q-2) (2*Q-2*r) w l p.val b.val) *
            (if a.val=b.val then (1:ℝ) else 0)) =
          coupledVector (2*Q-2) (2*Q-2*r) z k p.val a.val *
            coupledVector (2*Q-2) (2*Q-2*r) w l p.val a.val := by
      simp only [Fin.val_inj, mul_ite, mul_one, mul_zero]
      simp
    simp only [true_and, hsimp]
    rw [← gridInner_eq_fin_sum, coupledVector_gram hz₁ hz₂ hw₁ hw₂ hk hl]
  · simp [hrs]

 

theorem composedCoupledVector_eq_sphericalCopy {Q D T r : ℕ}
    (hr : r ≤ D) (hD : D ≤ T) (hT : T ≤ Q) (hor : Odd r)
    (b : Fin (2*Q-2+1) × IncreasingPair Q) :
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

 

theorem sphericalCopyCoefficient_highest_gram {Q D r s : ℕ}
    (hD : D ≤ Q) (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s) :
    (∑ b : Fin (2*Q-2+1) × IncreasingPair Q,
      sphericalCopyCoefficient Q D D r b.1.val b.2.val.1.val b.2.val.2.val *
      sphericalCopyCoefficient Q D D s b.1.val b.2.val.1.val b.2.val.2.val) =
        if r=s then 1 else 0 := by
  have hr0 : 1 ≤ r := by obtain ⟨a, ha⟩ := hor; omega
  have hs0 : 1 ≤ s := by obtain ⟨a, ha⟩ := hos; omega
  simp_rw [← composedCoupledVector_eq_sphericalCopy hr (le_refl D) hD hor,
    ← composedCoupledVector_eq_sphericalCopy hs (le_refl D) hD hos]
  rw [composedCoupledVector_gram (by omega) (by omega) hor hos
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  split_ifs <;> simp_all

end LaughlinFock
end

end OAI
