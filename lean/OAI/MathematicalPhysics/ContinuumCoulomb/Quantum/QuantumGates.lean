import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumVerifier
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinMatrixNorm

namespace OAI

/-! Unitarity of the actual finite H,T,CNOT verifier circuits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qmaHadamard_gram : qmaHadamard.conjTranspose * qmaHadamard = 1 := by
  have hraw : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose *
      !![1, 1; 1, -1] = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  unfold qmaHadamard
  rw [Matrix.conjTranspose_smul, bellScale_star, smul_mul_assoc, mul_smul_comm,
    hraw, smul_smul, smul_smul, mul_assoc, bellScale_twice_sq, one_smul]

theorem qmaPhaseT_gram : qmaPhaseT.conjTranspose * qmaPhaseT = 1 := by
  have hz : star (bellScale * (1 + Complex.I)) * (bellScale * (1 + Complex.I)) = 1 := by
    have hI : star Complex.I = -Complex.I := by simp
    simp only [star_mul, bellScale_star, star_add, star_one, hI]
    calc
      _ = bellScale ^ 2 * (1 - Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq, bellScale_sq]; norm_num
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [qmaPhaseT, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · norm_num [qmaPhaseT, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · norm_num [qmaPhaseT, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · change (qmaPhaseT.conjTranspose * qmaPhaseT) (1 : Fin 2) (1 : Fin 2) = 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change star (0 : ℂ) * 0 +
      star (bellScale * (1 + Complex.I)) * (bellScale * (1 + Complex.I)) = 1
    simpa only [star_zero, zero_mul, zero_add] using hz

theorem qmaLocal_gram (n : ℕ) (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.conjTranspose * M = 1) :
    (sourceTensor n (fun k => if k = i then M else 1)).conjTranspose *
      sourceTensor n (fun k => if k = i then M else 1) = 1 := by
  rw [sourceTensor_star, sourceTensor_mul]
  have h (k : Fin n) : (if k = i then M else 1).conjTranspose *
      (if k = i then M else 1) = 1 := by
    by_cases hk : k = i <;> simp [hk, hM]
  simp_rw [h]
  exact sourceTensor_one n

theorem qmaControlledNot_involutive (work : ℕ) (control target : Fin (work + 1))
    (hne : control ≠ target) : Function.Involutive (qmaControlledNot work control target) := by
  have hcontrol (s : SourceSpinBasis (work + 1)) :
      qmaControlledNot work control target s control = s control := by
    simp [qmaControlledNot, hne]
  intro s
  funext i
  change (if i = target ∧ qmaControlledNot work control target s control = 1 then
    Equiv.swap (0 : Fin 2) 1 (qmaControlledNot work control target s i)
    else qmaControlledNot work control target s i) = s i
  rw [hcontrol]
  unfold qmaControlledNot
  by_cases hi : i = target ∧ s control = 1
  · simp [hi, Equiv.swap_apply_self]
  · simp [hi]

theorem qmaPermutation_gram {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Function.Injective f) :
    let M : Matrix α α ℂ := fun s t => if s = f t then 1 else 0
    M.conjTranspose * M = 1 := by
  dsimp only
  ext s t
  change (∑ k : α, star (if k = f s then (1 : ℂ) else 0) *
    (if k = f t then 1 else 0)) = if s = t then 1 else 0
  simp [hf.eq_iff, eq_comm]

theorem qmaQubit_val {work i : ℕ} (hi : i < work + 1) : (qmaQubit work i).val = i :=
  Nat.mod_eq_of_lt hi

theorem qmaGateMatrix_gram (work : ℕ) (g : QMAGate) (hg : g.WellFormed (work + 1)) :
    (qmaGateMatrix work g).conjTranspose * qmaGateMatrix work g = 1 := by
  cases g with
  | hadamard i => exact qmaLocal_gram _ _ _ qmaHadamard_gram
  | phaseT i => exact qmaLocal_gram _ _ _ qmaPhaseT_gram
  | controlledNot i j =>
    have hne : qmaQubit work i ≠ qmaQubit work j := by
      intro h
      have hv := congrArg Fin.val h
      rw [qmaQubit_val hg.1, qmaQubit_val hg.2.1] at hv
      exact hg.2.2 hv
    exact qmaPermutation_gram _ (qmaControlledNot_involutive work _ _ hne).injective

theorem qmaCircuitMatrix_gram (c : QMACircuit) (hc : c.WellFormed) :
    (qmaCircuitMatrix c).conjTranspose * qmaCircuitMatrix c = 1 := by
  have hfold (gs : List QMAGate) (hgs : ∀ g ∈ gs, g.WellFormed (c.work + 1))
      (M : Matrix (SourceSpinBasis (c.work + 1)) (SourceSpinBasis (c.work + 1)) ℂ)
      (hM : M.conjTranspose * M = 1) :
      (gs.foldl (fun N g => qmaGateMatrix c.work g * N) M).conjTranspose *
        gs.foldl (fun N g => qmaGateMatrix c.work g * N) M = 1 := by
    induction gs generalizing M with
    | nil => exact hM
    | cons g gs ih =>
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      calc
        (qmaGateMatrix c.work g * M).conjTranspose * (qmaGateMatrix c.work g * M) =
            M.conjTranspose * ((qmaGateMatrix c.work g).conjTranspose * qmaGateMatrix c.work g) * M := by
          rw [Matrix.conjTranspose_mul]
          noncomm_ring
        _ = 1 := by rw [qmaGateMatrix_gram c.work g (hgs g (List.mem_cons_self)), mul_one, hM]
  exact hfold c.gates hc.2 1 (by simp)

theorem qmaCircuit_preserves_norm (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis (c.work + 1))) :
    ‖spinMatrixOperator (qmaCircuitMatrix c) psi‖ = ‖psi‖ :=
  spinMatrixOperator_unitary_norm_map _ (qmaCircuitMatrix_gram c hc) psi

end ContinuumCoulomb

end

end OAI
