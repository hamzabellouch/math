import OAI.Analysis.Laughlin.Asymptotics.FiniteReindex
import OAI.Analysis.Laughlin.ThreeBody.ProjectorBound

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem threeBody_dimension_ratio (Q z : ℕ) (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    ((coupledWeight Q z+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) =
      (3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1) := by
  have hn : ((coupledWeight Q z+1 : ℕ) : ℝ)=3*(Q : ℝ)-1-2*(z : ℝ) := by
    unfold coupledWeight
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 3*Q)]
    push_cast
    ring
  have hd : ((2*Q-2+1 : ℕ) : ℝ)=2*(Q : ℝ)-1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  rw [hn,hd]

theorem physical_threeBody_tail_sum (Q : ℕ) (hQ : 4 ≤ Q) (x : Space Q) :
    -(deltaFormula Q * sourceFockEnergy Q x) ≤
      ∑ z : Fin (Q+1), if 16 ≤ z.val then gramEigenvalueFormula Q z.val *
        (contractionForm Q (sourceThreeEnd Q)
          ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0 := by
  let P := fun z : Fin (Q+1) => (contractionForm Q (sourceThreeEnd Q)
    ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re
  have hP (z : Fin (Q+1)) : 0 ≤ P z := physical_threeBody_projector_nonneg Q (by omega) z x
  have hb (z : Fin (Q+1)) : P z ≤
      ((3*(Q : ℝ)-1-2*(z.val : ℝ))/(2*(Q : ℝ)-1))*
        (z.val+1 : ℕ)*sourceFockEnergy Q x := by
    simpa only [threeBody_dimension_ratio Q z.val hQ (by omega)] using
      physical_threeBody_projector_bound Q (by omega) z x
  have ht (z : Fin (Q+1)) :
      -(if 17 ≤ z.val ∧ Odd z.val then tailWeight Q z.val else 0) * sourceFockEnergy Q x ≤
        if 16 ≤ z.val then gramEigenvalueFormula Q z.val * P z else 0 := by
    by_cases hz : 16 ≤ z.val
    · rw [ite_eq_left hz]
      by_cases ho : Odd z.val
      · have hz17 : 17 ≤ z.val := by obtain ⟨k,hk⟩ := ho; omega
        rw [ite_eq_left ⟨hz17,ho⟩]
        have h₁ := mul_le_mul_of_nonneg_left (hb z) (abs_nonneg (gramEigenvalueFormula Q z.val))
        have h₂ := mul_le_mul_of_nonneg_right (neg_abs_le (gramEigenvalueFormula Q z.val)) (hP z)
        unfold tailWeight
        push_cast at h₁ ⊢
        nlinarith
      · rw [ite_eq_right (by tauto)]
        have he : Even z.val := Nat.not_odd_iff_even.mp ho
        have hpow : (-1 : ℝ)^z.val=1 := he.neg_one_pow
        have hg : 0 ≤ gramEigenvalueFormula Q z.val := by
          unfold gramEigenvalueFormula
          rw [hpow,one_mul]
          exact mul_nonneg (by unfold fallingRatio; positivity) (tail_bracket_bounds hQ hz (by omega)).1
        simpa using mul_nonneg hg (hP z)
    · have hn : ¬ (17 ≤ z.val ∧ Odd z.val) := by omega
      simp only [ite_eq_right hz,ite_eq_right hn,neg_zero,zero_mul,le_refl]
  have hs : (∑ z : Fin (Q+1), if 17 ≤ z.val ∧ Odd z.val then tailWeight Q z.val else 0)=deltaFormula Q := by
    rw [Fin.sum_univ_eq_sum_range (fun z => if 17 ≤ z ∧ Odd z then tailWeight Q z else 0) (Q+1),
      ← Finset.sum_filter,← deltaFormula_eq_odd_finite_sum]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z hz => ht z)
  simpa only [← Finset.sum_mul,Finset.sum_neg_distrib,hs,neg_mul] using h

theorem physical_threeBody_Fock_tail (Q : ℕ) (hQ : 4 ≤ Q) (x : Space Q) :
    -(deltaFormula Q * sourceFockEnergy Q x) ≤
      (contractionForm Q (sourceThreeEnd Q)
        (∑ z : Fin (Q+1), if 16 ≤ z.val then (gramEigenvalueFormula Q z.val : ℂ) •
          (threeSpinProjector Q (by omega) z).map Complex.ofReal else 0) x).re := by
  rw [contractionForm_sum,Complex.re_sum]
  have hz : contractionForm Q (sourceThreeEnd Q) (0 : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) x=0 := by
    simp [contractionForm]
  apply (physical_threeBody_tail_sum Q hQ x).trans_eq
  apply Finset.sum_congr rfl
  intro z hz'
  by_cases h16 : 16 ≤ z.val
  · simp only [ite_eq_left h16,contractionForm_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  · simp only [ite_eq_right h16,hz,Complex.zero_re]

end Laughlin.Fock

end OAI
