import OAI.Analysis.IrrationalRotation.Operators.Conjugation
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentCommuting

namespace OAI

noncomputable section
open scoped BigOperators Topology
namespace Invariant233
namespace ConjugationSupport

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def leftMul (a : A) : A →L[ℂ] A := ContinuousLinearMap.mul ℂ A a

def rightMul (a : A) : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).flip a

@[simp] theorem leftMul_apply (a x : A) : leftMul a x = a * x := rfl
@[simp] theorem rightMul_apply (a x : A) : rightMul a x = x * a := rfl

@[simp] theorem leftMul_pow (a : A) (n : ℕ) : (leftMul a) ^ n = leftMul (a ^ n) := by
  induction n with
  | zero => ext x; simp
  | succ n ih => ext x; simp [pow_succ, ih, mul_assoc]

@[simp] theorem rightMul_pow (a : A) (n : ℕ) : (rightMul a) ^ n = rightMul (a ^ n) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    ext x
    simp only [pow_succ, mul_apply_eq_comp, ih, rightMul_apply]
    rw [mul_assoc, ← pow_succ', pow_succ]

theorem leftMul_commute_rightMul (a b : A) : Commute (leftMul a) (rightMul b) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [mul_assoc]

theorem norm_leftMul_le (a : A) : ‖leftMul a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le ℂ A a

theorem norm_rightMul_le (a : A) : ‖rightMul a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (norm_mul_le x a).trans_eq (mul_comm _ _)

theorem normQuasinilpotent_leftMul {a : A} (ha : NormQuasinilpotent a) :
    NormQuasinilpotent (leftMul a) := by
  apply root_tendsto_zero_of_geometric_bounds _ (fun _ => norm_nonneg _)
  intro r hr
  obtain ⟨C, hC, hb⟩ := ha.geometric_bound r hr
  refine ⟨C, hC, fun n => ?_⟩
  rw [leftMul_pow]
  exact (norm_leftMul_le _).trans (hb n)

theorem normQuasinilpotent_rightMul {a : A} (ha : NormQuasinilpotent a) :
    NormQuasinilpotent (rightMul a) := by
  apply root_tendsto_zero_of_geometric_bounds _ (fun _ => norm_nonneg _)
  intro r hr
  obtain ⟨C, hC, hb⟩ := ha.geometric_bound r hr
  refine ⟨C, hC, fun n => ?_⟩
  rw [rightMul_pow]
  exact (norm_rightMul_le _).trans (hb n)

theorem mul_left_right_pow_apply (a b x : A) (n : ℕ) :
    ((leftMul a * rightMul b) ^ n) x = a ^ n * x * b ^ n := by
  rw [(leftMul_commute_rightMul a b).mul_pow, leftMul_pow, rightMul_pow]
  simp [mul_assoc]

@[simp] theorem leftMul_one : leftMul (1 : A) = 1 := by ext x; simp
@[simp] theorem rightMul_one : rightMul (1 : A) = 1 := by ext x; simp
@[simp] theorem leftMul_add (a b : A) : leftMul (a + b) = leftMul a + leftMul b := by
  ext x
  simp [add_mul]
@[simp] theorem rightMul_add (a b : A) : rightMul (a + b) = rightMul a + rightMul b := by
  ext x
  simp [mul_add]

theorem sub_one_pow_apply (B : A →L[ℂ] A) (x : A) (n : ℕ) :
    ((B - 1) ^ n) x = ∑ j ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ j * (n.choose j : ℂ)) • ((B ^ (n - j)) x) := by
  have hexp : (B - 1) ^ n = ∑ j ∈ Finset.range (n + 1),
      n.choose j • ((-1 : A →L[ℂ] A) ^ j * B ^ (n - j)) := by
    rw [show B - 1 = -1 + B by abel]
    simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
      (Commute.neg_one_left B).add_pow' n
  rw [hexp]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hnegpow : ∀ (k : ℕ) (y : A), ((-1 : A →L[ℂ] A) ^ k) y = (-1 : ℂ) ^ k • y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; simp [pow_succ', mul_apply_eq_comp, ih]
  simp only [smul_apply, mul_apply_eq_comp, hnegpow]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  ring

end ConjugationSupport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ConjugationSupport

def conjugationDefectMap (C : HilbertConjugation H) (T : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  leftMul (star T) * rightMul (C.conjugate T) - 1

theorem conjugationDefectMap_one_add (C : HilbertConjugation H) (Q : H →L[ℂ] H) :
    conjugationDefectMap C (1 + Q) =
      leftMul (star Q) + rightMul (C.conjugate Q) +
        leftMul (star Q) * rightMul (C.conjugate Q) := by
  simp only [conjugationDefectMap, star_add, star_one,
    HilbertConjugation.conjugate_add, HilbertConjugation.conjugate_one,
    leftMul_add, rightMul_add, leftMul_one, rightMul_one]
  noncomm_ring

theorem normQuasinilpotent_conjugationDefectMap_one_add
    (C : HilbertConjugation H) {Q : H →L[ℂ] H} (hQ : NormQuasinilpotent Q) :
    NormQuasinilpotent (conjugationDefectMap C (1 + Q)) := by
  have hnorm : ∀ n : ℕ, ‖(star Q) ^ n‖ = ‖Q ^ n‖ := by
    intro n
    rw [← star_pow]
    exact ContinuousLinearMap.adjoint.norm_map _
  have hstar : NormQuasinilpotent (star Q) := by
    simpa only [NormQuasinilpotent, hnorm] using hQ
  have hL := normQuasinilpotent_leftMul hstar
  have hR := normQuasinilpotent_rightMul (C.normQuasinilpotent_conjugate hQ)
  have hcomm := leftMul_commute_rightMul (star Q) (C.conjugate Q)
  rw [conjugationDefectMap_one_add]
  apply (hL.add_of_commute hR hcomm).add_of_commute (hL.mul_of_commute hR hcomm)
  exact ((Commute.refl _).mul_right hcomm).add_left
    (hcomm.symm.mul_right (Commute.refl _))

theorem conjugationDefect_eq_power_apply (C : HilbertConjugation H)
    (T : H →L[ℂ] H) (m : ℕ) :
    conjugationDefect C T m = ((conjugationDefectMap C T) ^ m) 1 := by
  simp only [conjugationDefectMap, sub_one_pow_apply, conjugationDefect,
    mul_left_right_pow_apply, mul_one, HilbertConjugation.conjugate_pow]

theorem isInfiniteConjugationIsometry_one_add (C : HilbertConjugation H)
    {Q : H →L[ℂ] H} (hQ : NormQuasinilpotent Q) :
    IsInfiniteConjugationIsometry C (1 + Q) := by
  apply root_tendsto_zero_of_geometric_bounds _ (fun _ => norm_nonneg _)
  intro r hr
  obtain ⟨K, hK, hb⟩ :=
    (normQuasinilpotent_conjugationDefectMap_one_add C hQ).geometric_bound r hr
  refine ⟨K * (‖(1 : H →L[ℂ] H)‖ + 1), by positivity, fun n => ?_⟩
  rw [conjugationDefect_eq_power_apply]
  calc
    ‖((conjugationDefectMap C (1 + Q)) ^ n) 1‖
        ≤ ‖(conjugationDefectMap C (1 + Q)) ^ n‖ * ‖(1 : H →L[ℂ] H)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (K * r ^ n) * (‖(1 : H →L[ℂ] H)‖ + 1) :=
      mul_le_mul (hb n) (by linarith) (norm_nonneg _) (by positivity)
    _ = K * (‖(1 : H →L[ℂ] H)‖ + 1) * r ^ n := by ring

end Invariant233

end

end OAI
