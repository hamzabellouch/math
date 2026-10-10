import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedPauli
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedModel

namespace OAI

/-! Actual ordered history cores have exact four-rational entries.  The
propagation Gram is formed on its at-most-five-site core; the construction
does not sum over spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def denote {α β : Type} (A : Matrix α β Scalar) : Matrix α β ℂ :=
  fun s t => value (A s t)

def matMul {α β γ : Type} [Fintype β]
    (A : Matrix α β Scalar) (B : Matrix β γ Scalar) : Matrix α γ Scalar :=
  fun s t => finiteSum (fun u => mul (A s u) (B u t))

def adjoint {α β : Type} (A : Matrix α β Scalar) : Matrix β α Scalar :=
  fun s t => conj (A t s)

theorem denote_mul {α β γ : Type} [Fintype β]
    (A : Matrix α β Scalar) (B : Matrix β γ Scalar) :
    denote (matMul A B) = denote A * denote B := by
  ext s t
  simp only [denote,matMul,value_finiteSum,value_mul,Matrix.mul_apply]

theorem denote_adjoint {α β : Type} (A : Matrix α β Scalar) :
    denote (adjoint A) = (denote A).conjTranspose := by
  ext s t
  simp only [denote,adjoint,value_conj,Matrix.conjTranspose_apply]

def hadamard (s t : Fin 2) : Scalar :=
  mul sqrtHalf (rat (if s = 1 ∧ t = 1 then -1 else 1))

def phaseT (s t : Fin 2) : Scalar :=
  if s = t then (if s = 0 then rat 1 else mul sqrtHalf (add (rat 1) imaginary)) else rat 0

theorem value_hadamard (s t : Fin 2) : value (hadamard s t) = qmaHadamard s t := by
  fin_cases s <;> fin_cases t <;> simp [hadamard,qmaHadamard]

theorem value_phaseT (s t : Fin 2) : value (phaseT s t) = qmaPhaseT s t := by
  fin_cases s <;> fin_cases t <;> simp [phaseT,qmaPhaseT]

def identity {α : Type} [DecidableEq α] (s t : α) : Scalar := rat (if s = t then 1 else 0)

theorem value_identity {α : Type} [DecidableEq α] (s t : α) :
    value (identity s t) = (1 : Matrix α α ℂ) s t := by
  by_cases h : s = t <;> simp [identity,Matrix.one_apply,h]

def gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) : Scalar :=
  match g with
  | .hadamard i => finiteProduct (fun k =>
      if k = qmaQubit work i then hadamard (s k) (t k) else identity (s k) (t k))
  | .phaseT i => finiteProduct (fun k =>
      if k = qmaQubit work i then phaseT (s k) (t k) else identity (s k) (t k))
  | .controlledNot i j => rat
      (if s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t then 1 else 0)

theorem value_gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) :
    value (gate work g s t) = qmaGateMatrix work g s t := by
  cases g with
  | hadamard i =>
    rw [gate,value_finiteProduct]
    unfold qmaGateMatrix sourceTensor
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = qmaQubit work i
    · simp only [h,ite_true,value_hadamard]
    · simp only [h,ite_false,value_identity]
  | phaseT i =>
    rw [gate,value_finiteProduct]
    unfold qmaGateMatrix sourceTensor
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = qmaQubit work i
    · simp only [h,ite_true,value_phaseT]
    · simp only [h,ite_false,value_identity]
  | controlledNot i j =>
    by_cases h : s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t
    <;> simp [gate,qmaGateMatrix,h]

def delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) : Scalar :=
  if QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
      s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0 then
    sub (identity s (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) r))
      (mul (identity (s ∘ Sum.inl) (r ∘ Sum.inl))
        (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr)))
  else rat 0

theorem value_delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) :
    value (delta c t s r) = qmaLocalPropagationDelta c t s r := by
  rw [qmaLocalPropagationDelta,qmaGuardProjection,Matrix.diagonal_mul]
  by_cases h : QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
      s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0
  · simp [delta,h,Matrix.sub_apply,qmaBitFlipMatrix,qmaJoinMatrix,
      Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,qmaStepMatrix,
      value_identity,value_gate]
    rfl
  · simp [delta,h]

def deltaCore (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMASupportBasis (qmaPropagationSites c t))
      (QMASupportBasis (qmaPropagationSites c t)) Scalar :=
  fun s r => delta c t (qmaSupportExtend _ s) (qmaSupportExtend _ r)

theorem denote_deltaCore (c : QMACircuit) (t : Fin c.gates.length) :
    denote (deltaCore c t) = qmaLocalCore (qmaPropagationSites c t)
      (qmaLocalPropagationDelta c t) := by
  ext s r
  exact value_delta c t _ _

theorem core_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : Finset ι} {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn S B) :
    qmaLocalCore S (A*B) = qmaLocalCore S A*qmaLocalCore S B := by
  obtain ⟨A,rfl⟩ := hA
  obtain ⟨B,rfl⟩ := hB
  rw [← qmaLocalLift_mul,qmaLocalCore_lift,qmaLocalCore_lift,qmaLocalCore_lift]

theorem core_adjoint {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) :
    qmaLocalCore S A.conjTranspose = (qmaLocalCore S A).conjTranspose := by
  obtain ⟨A,rfl⟩ := hA
  rw [← qmaLocalLift_adjoint,qmaLocalCore_lift,qmaLocalCore_lift]

def propagationCore (c : QMACircuit) (t : Fin c.gates.length) :=
  matMul (adjoint (deltaCore c t)) (deltaCore c t)

theorem denote_propagationCore (c : QMACircuit) (t : Fin c.gates.length) :
    denote (propagationCore c t) = qmaLocalCore (qmaPropagationSites c t)
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t) := by
  rw [propagationCore,denote_mul,denote_adjoint,denote_deltaCore,
    core_mul (qmaLocalPropagationDelta_local c t).adjoint (qmaLocalPropagationDelta_local c t),
    core_adjoint (qmaLocalPropagationDelta_local c t)]

def lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (s t : ι → Fin 2) : Scalar :=
  mul (A (fun i => s i.val) (fun i => t i.val))
    (identity (fun i : {i // i ∉ S} => s i.val) (fun i => t i.val))

theorem denote_lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar) :
    denote (lift S A) = qmaLocalLift S (denote A) := by
  ext s t
  simp only [denote,lift,value_mul,value_identity,Matrix.one_apply,qmaLocalLift_apply]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
