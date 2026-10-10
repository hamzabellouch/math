import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumVerifier

namespace OAI

/-! Exact unitarity of the fixed verifier gates, needed for the
circuit-to-Hamiltonian construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qmaHadamard_gram : qmaHadamard.conjTranspose * qmaHadamard = 1 := by
  have hs : (starRingEnd ℂ) bellScale = bellScale := bellScale_star
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaHadamard,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ,bellScale_star,star_mul,hs] <;>
    ring_nf <;> norm_num [bellScale_sq,hs]

theorem qmaPhaseT_gram : qmaPhaseT.conjTranspose * qmaPhaseT = 1 := by
  have hs : (starRingEnd ℂ) bellScale = bellScale := bellScale_star
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaPhaseT,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ,bellScale_star,star_mul,hs]
  ring_nf
  norm_num [bellScale_sq,hs]

theorem sourceTensor_conjTranspose (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor n M).conjTranspose = sourceTensor n (fun i => (M i).conjTranspose) := by
  ext s t
  simp [sourceTensor,Matrix.conjTranspose_apply]

theorem sourceTensor_gram (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ i, (M i).conjTranspose * M i = 1) :
    (sourceTensor n M).conjTranspose * sourceTensor n M = 1 := by
  rw [sourceTensor_conjTranspose,sourceTensor_mul]
  simp_rw [hM]
  exact sourceTensor_one n

theorem qmaControlledNot_involutive (work : ℕ) (control target : Fin (work+1))
    (hct : control ≠ target) : Function.Involutive (qmaControlledNot work control target) := by
  intro s
  have hc : qmaControlledNot work control target s control = s control := by
    simp [qmaControlledNot,hct]
  funext i
  change (if i = target ∧ qmaControlledNot work control target s control = 1 then
    Equiv.swap (0:Fin 2) 1 (qmaControlledNot work control target s i)
    else qmaControlledNot work control target s i) = s i
  rw [hc]
  by_cases hi : i = target
  · subst i
    by_cases hs : s control = 1 <;> simp [qmaControlledNot,hs]
  · simp [hi,qmaControlledNot]

theorem qmaGateMatrix_gram (work : ℕ) (g : QMAGate) (hg : g.WellFormed (work+1)) :
    (qmaGateMatrix work g).conjTranspose * qmaGateMatrix work g = 1 := by
  classical
  cases g with
  | hadamard i =>
    apply sourceTensor_gram
    intro k
    split_ifs <;> simp [qmaHadamard_gram]
  | phaseT i =>
    apply sourceTensor_gram
    intro k
    split_ifs <;> simp [qmaPhaseT_gram]
  | controlledNot i j =>
    have hij : qmaQubit work i ≠ qmaQubit work j := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1] at hval
      exact hg.2.2 hval
    have hf := qmaControlledNot_involutive work (qmaQubit work i) (qmaQubit work j) hij
    ext s t
    change (∑ b, star (if b = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) s
        then (1:ℂ) else 0) *
      (if b = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t then 1 else 0)) =
      if s = t then 1 else 0
    simp only [apply_ite,star_one,star_zero]
    rw [Finset.sum_eq_single (qmaControlledNot work (qmaQubit work i) (qmaQubit work j) s)]
    · simp [hf.injective.eq_iff]
    · intro b _hb hbs
      simp [hbs]
    · simp

theorem qmaCircuitMatrix_gram (c : QMACircuit) (hc : c.WellFormed) :
    (qmaCircuitMatrix c).conjTranspose * qmaCircuitMatrix c = 1 := by
  have hfold (gs : List QMAGate) (hgs : ∀ g ∈ gs, g.WellFormed (c.work+1))
      (M : Matrix (SourceSpinBasis (c.work+1)) (SourceSpinBasis (c.work+1)) ℂ)
      (hM : M.conjTranspose*M = 1) :
      (gs.foldl (fun A g => qmaGateMatrix c.work g*A) M).conjTranspose *
        gs.foldl (fun A g => qmaGateMatrix c.work g*A) M = 1 := by
    induction gs generalizing M with
    | nil => exact hM
    | cons g gs ih =>
      apply ih (fun q hq => hgs q (List.mem_cons_of_mem g hq))
      rw [Matrix.conjTranspose_mul]
      calc
        M.conjTranspose*(qmaGateMatrix c.work g).conjTranspose*(qmaGateMatrix c.work g*M) =
            M.conjTranspose*((qmaGateMatrix c.work g).conjTranspose*qmaGateMatrix c.work g)*M := by
              noncomm_ring
        _ = 1 := by rw [qmaGateMatrix_gram c.work g (hgs g (List.mem_cons_self)),mul_one,hM]
  exact hfold c.gates hc.2 1 (by simp)

end ContinuumCoulomb

end

end OAI
