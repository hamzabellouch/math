import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.GlobalSinglet

namespace OAI

/-! Exact simultaneous singlet-penalty diagonalization and inverse compression.
All tensor matrices here act on the complete mediator configuration basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

/-- Tensor product over the actual four-state mediator pairs. -/
def mediatorTensor (r : ℕ) (M : Fin r → Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ := fun a b => ∏ e, M e (a e) (b e)

theorem mediatorTensor_one (r : ℕ) : mediatorTensor r (fun _ => 1) = 1 := by
  ext a b
  simpa only [mediatorTensor, Matrix.one_apply] using product_delta r a b

theorem mediatorTensor_mul (r : ℕ) (M N : Fin r → Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorTensor r M * mediatorTensor r N = mediatorTensor r (fun e => M e * N e) := by
  ext a b
  simp only [Matrix.mul_apply, mediatorTensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun e s => M e (a e) s * N e s (b e))).symm

theorem mediatorTensor_star (r : ℕ) (M : Fin r → Matrix (Fin 4) (Fin 4) ℂ) :
    (mediatorTensor r M).conjTranspose = mediatorTensor r (fun e => (M e).conjTranspose) := by
  ext a b
  simp only [mediatorTensor, Matrix.conjTranspose_apply, star_prod]

theorem mediatorTensor_diagonal (r : ℕ) (d : Fin r → Fin 4 → ℂ) :
    mediatorTensor r (fun e => Matrix.diagonal (d e)) =
      Matrix.diagonal (fun a => ∏ e, d e (a e)) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [mediatorTensor]
  · obtain ⟨e, he⟩ := Function.ne_iff.mp hab
    simp only [Matrix.diagonal_apply, ite_eq_right hab, mediatorTensor]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- An operator acting on one actual fresh pair, with identity on all others. -/
def mediatorLocal (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  mediatorTensor r (fun f => if f = e then M else 1)

theorem mediatorLocal_apply (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (a b : MediatorBasis r) :
    mediatorLocal r e M a b = M (a e) (b e) *
      ∏ f ∈ Finset.univ.erase e, if a f = b f then (1 : ℂ) else 0 := by
  classical
  unfold mediatorLocal mediatorTensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  simp only [ite_eq_right (Finset.mem_erase.mp hf).1, Matrix.one_apply]

theorem mediatorLocal_vacuum (r : ℕ) (e : Fin r) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e M (mediatorVacuum r) (mediatorVacuum r) = M 0 0 := by
  simp [mediatorLocal_apply, mediatorVacuum]

theorem mediatorLocal_mul_same (r : ℕ) (e : Fin r)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e M * mediatorLocal r e N = mediatorLocal r e (M * N) := by
  unfold mediatorLocal
  rw [mediatorTensor_mul]
  congr 1
  funext f
  by_cases h : f = e <;> simp [h]

theorem mediatorLocal_diagonal (r : ℕ) (e : Fin r) (d : Fin 4 → ℂ) :
    mediatorLocal r e (Matrix.diagonal d) = Matrix.diagonal (fun a => d (a e)) := by
  classical
  have h (f : Fin r) :
      (if f = e then Matrix.diagonal d else (1 : Matrix (Fin 4) (Fin 4) ℂ)) =
        Matrix.diagonal (fun s => if f = e then d s else 1) := by
    by_cases hf : f = e <;> simp [hf]
  unfold mediatorLocal
  simp_rw [h]
  rw [mediatorTensor_diagonal]
  congr 1
  funext a
  exact Fintype.prod_ite_eq' e (fun f => d (a f))

/-- Conjugating the actual physical one-pair operator by the global Bell
basis gives exactly the same local operator in Bell coordinates. -/
theorem mediatorLocal_bellTransform (r : ℕ) (e : Fin r)
    (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (globalBellMatrix r).conjTranspose * mediatorLocal r e M * globalBellMatrix r =
      mediatorLocal r e (bellTransform M) := by
  change (mediatorTensor r (fun _ => bellMatrix)).conjTranspose *
    mediatorTensor r (fun f => if f = e then M else 1) *
      mediatorTensor r (fun _ => bellMatrix) = _
  rw [mediatorTensor_star, mediatorTensor_mul, mediatorTensor_mul]
  unfold mediatorLocal
  congr 1
  funext f
  by_cases hf : f = e
  · simp only [ite_eq_left hf, bellTransform]
  · simp only [ite_eq_right hf, mul_one, bellMatrix_gram]

theorem bellTransform_penalty :
    bellTransform (heisenberg + (3 : ℂ) • 1) =
      Matrix.diagonal (fun a : Fin 4 => if a = 0 then (0 : ℂ) else 4) := by
  have hH : bellTransform heisenberg =
      Matrix.diagonal (fun a : Fin 4 => if a = 0 then (-3 : ℂ) else 1) := by
    unfold bellTransform
    rw [mul_assoc, bellMatrix_heisenberg, ← mul_assoc, bellMatrix_gram, one_mul]
  have hsum : bellTransform (heisenberg + (3 : ℂ) • 1) =
      bellTransform heisenberg + (3 : ℂ) • 1 := by
    unfold bellTransform
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      bellMatrix_gram]
  rw [hsum, hH]
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases ha : a = 0 <;> norm_num [ha]
  · simp [hab]

/-- The physical central-bond sum, with its singlet scalar shifts. -/
def physicalMediatorPenalty (r : ℕ) (Delta : ℝ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  (Delta : ℂ) • ∑ e, mediatorLocal r e (heisenberg + (3 : ℂ) • 1)

theorem mediatorExcitationNumber_sum (r : ℕ) (a : MediatorBasis r) :
    (∑ e : Fin r, if a e = 0 then (0 : ℂ) else 1) =
      (mediatorExcitationNumber r a : ℂ) := by
  classical
  simp [mediatorExcitationNumber, Finset.card_filter]

/-- Exact diagonalization of the entire simultaneous central Hamiltonian. -/
theorem physicalMediatorPenalty_diagonal (r : ℕ) (Delta : ℝ) :
    (globalBellMatrix r).conjTranspose * physicalMediatorPenalty r Delta * globalBellMatrix r =
      Matrix.diagonal (fun a => (mediatorPenaltyWeight r Delta a : ℂ)) := by
  unfold physicalMediatorPenalty
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  simp_rw [mediatorLocal_bellTransform, bellTransform_penalty, mediatorLocal_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.diagonal_apply, ite_true]
    have hsum : (∑ e : Fin r, if a e = 0 then (0 : ℂ) else 4) =
        4 * (mediatorExcitationNumber r a : ℂ) := by
      rw [← mediatorExcitationNumber_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    rw [hsum]
    unfold mediatorPenaltyWeight
    push_cast
    ring
  · simp [Matrix.sum_apply, hab]

/-- Full inverse on the triplet complement and zero on the singlet kernel. -/
def mediatorInverseWeight (r : ℕ) (Delta : ℝ) (a : MediatorBasis r) : ℂ :=
  if a = mediatorVacuum r then 0 else ((mediatorPenaltyWeight r Delta a)⁻¹ : ℝ)

def mediatorInverseMatrix (r : ℕ) (Delta : ℝ) :
    Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  Matrix.diagonal (mediatorInverseWeight r Delta)

theorem mediatorLocal_column_support (r : ℕ) (e : Fin r)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (a : MediatorBasis r)
    (ha : mediatorLocal r e N a (mediatorVacuum r) ≠ 0) :
    ∀ f, f ≠ e → a f = 0 := by
  classical
  intro f hf
  by_contra hzero
  apply ha
  rw [mediatorLocal_apply]
  have hz : (∏ j ∈ Finset.univ.erase e,
      if a j = mediatorVacuum r j then (1 : ℂ) else 0) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hf, Finset.mem_univ f⟩)
    simp [mediatorVacuum, hzero]
  rw [hz, mul_zero]

theorem mediatorLocal_column_excitation (r : ℕ) (e : Fin r)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : N 0 0 = 0) (a : MediatorBasis r)
    (ha : mediatorLocal r e N a (mediatorVacuum r) ≠ 0) :
    a ≠ mediatorVacuum r ∧ mediatorExcitationNumber r a = 1 := by
  classical
  have havac : a ≠ mediatorVacuum r := by
    intro h
    subst a
    exact ha (by rw [mediatorLocal_vacuum, hN])
  have hs := mediatorLocal_column_support r e N a ha
  have he : a e ≠ 0 := by
    intro hzero
    apply havac
    funext f
    by_cases hf : f = e
    · simpa [hf, mediatorVacuum] using hzero
    · exact hs f hf
  refine ⟨havac, ?_⟩
  have hset : Finset.univ.filter (fun f => a f ≠ 0) = {e} := by
    ext f
    by_cases hf : f = e
    · simp [hf, he]
    · simp [hf, hs f hf]
  simp only [mediatorExcitationNumber, hset, Finset.card_singleton]

/-- Every single fresh-pair excitation has the same denominator four Delta. -/
theorem mediatorInverse_local_column (r : ℕ) (Delta : ℝ) (e : Fin r)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : N 0 0 = 0) (a : MediatorBasis r) :
    mediatorInverseWeight r Delta a * mediatorLocal r e N a (mediatorVacuum r) =
      ((4 * Delta)⁻¹ : ℝ) * mediatorLocal r e N a (mediatorVacuum r) := by
  by_cases ha : mediatorLocal r e N a (mediatorVacuum r) = 0
  · simp only [ha, mul_zero]
  · obtain ⟨havac, hcount⟩ := mediatorLocal_column_excitation r e N hN a ha
    simp only [mediatorInverseWeight, ite_eq_right havac, mediatorPenaltyWeight,
      hcount, Nat.cast_one, mul_one]

theorem mediatorLocal_cross_vacuum (r : ℕ) (e f : Fin r) (hef : e ≠ f)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) (hM : M 0 0 = 0) :
    (mediatorLocal r e M * mediatorLocal r f N)
      (mediatorVacuum r) (mediatorVacuum r) = 0 := by
  classical
  unfold mediatorLocal
  rw [mediatorTensor_mul]
  unfold mediatorTensor
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [hef, mediatorVacuum, hM]

/-- Exact inverse-compressed contraction. Different fresh pairs cancel;
the same pair has the actual excitation denominator four Delta. -/
theorem mediator_inverse_compression (r : ℕ) (Delta : ℝ) (e f : Fin r)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) (hM : M 0 0 = 0) (hN : N 0 0 = 0) :
    (mediatorLocal r e M * mediatorInverseMatrix r Delta * mediatorLocal r f N)
      (mediatorVacuum r) (mediatorVacuum r) =
      if e = f then ((4 * Delta)⁻¹ : ℝ) * (M * N) 0 0 else 0 := by
  classical
  have hinv : (mediatorLocal r e M * mediatorInverseMatrix r Delta * mediatorLocal r f N)
      (mediatorVacuum r) (mediatorVacuum r) =
      ((4 * Delta)⁻¹ : ℝ) * (mediatorLocal r e M * mediatorLocal r f N)
        (mediatorVacuum r) (mediatorVacuum r) := by
    rw [mul_assoc]
    rw [Matrix.mul_apply]
    simp_rw [mediatorInverseMatrix, Matrix.diagonal_mul,
      mediatorInverse_local_column r Delta f N hN]
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hinv]
  by_cases hef : e = f
  · subst f
    rw [mediatorLocal_mul_same, mediatorLocal_vacuum, ite_eq_left (Eq.refl e)]
  · rw [mediatorLocal_cross_vacuum r e f hef M N hM, mul_zero, ite_eq_right hef]


theorem bell_second_second_zero (μ ν : Fin 3) :
    (bellTransform (secondPauli μ) * bellTransform (secondPauli ν)) 0 0 =
      if μ = ν then 1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_second_second]
  split_ifs <;> norm_num

theorem bell_second_first_zero (μ ν : Fin 3) :
    (bellTransform (secondPauli μ) * bellTransform (firstPauli ν)) 0 0 =
      if μ = ν then -1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_second_first]
  split_ifs <;> norm_num

/-- Actual Pauli action on either member of a mediator pair in Bell coordinates. -/
def bellMemberPauli (member : Fin 2) (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  if member = 0 then bellTransform (firstPauli μ) else bellTransform (secondPauli μ)

theorem bellMemberPauli_zero (member : Fin 2) (μ : Fin 3) :
    bellMemberPauli member μ 0 0 = 0 := by
  unfold bellMemberPauli
  split_ifs
  · exact bell_first_pauli_zero μ
  · exact bell_second_pauli_zero μ

theorem bellMemberPauli_product (member other : Fin 2) (μ ν : Fin 3) :
    (bellMemberPauli member μ * bellMemberPauli other ν) 0 0 =
      if μ = ν then (if member = other then 1 else -1) else 0 := by
  fin_cases member <;> fin_cases other <;>
    simp [bellMemberPauli, bell_first_first_zero, bell_first_second_zero,
      bell_second_first_zero, bell_second_second_zero]

/-- The exact global inverse contraction, with arbitrary spectator mediator
pairs: different pairs or Pauli axes vanish, and opposite members change sign. -/
theorem mediator_pauli_inverse_compression (r : ℕ) (Delta : ℝ) (e f : Fin r)
    (member other : Fin 2) (μ ν : Fin 3) :
    (mediatorLocal r e (bellMemberPauli member μ) * mediatorInverseMatrix r Delta *
      mediatorLocal r f (bellMemberPauli other ν)) (mediatorVacuum r) (mediatorVacuum r) =
      if e = f ∧ μ = ν then
        ((4 * Delta)⁻¹ : ℝ) * (if member = other then (1 : ℂ) else -1) else 0 := by
  rw [mediator_inverse_compression r Delta e f _ _
    (bellMemberPauli_zero member μ) (bellMemberPauli_zero other ν), bellMemberPauli_product]
  by_cases hef : e = f <;> by_cases hμν : μ = ν <;> simp [hef, hμν]

end ContinuumCoulomb

end

end OAI
