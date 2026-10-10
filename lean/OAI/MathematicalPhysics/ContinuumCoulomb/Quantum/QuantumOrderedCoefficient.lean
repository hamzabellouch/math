import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicHistory

namespace OAI

/-! Exact rational-register tables for every actual ordered history term.
Only the propagation core is multiplied, so its summation has at most
32 states regardless of the number of spectator qubits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

def diagonal {α : Type} [DecidableEq α] (f : α → ℚ) : Matrix α α Scalar :=
  fun s t => if s = t then rat (f s) else rat 0

theorem denote_diagonal {α : Type} [DecidableEq α] (f : α → ℚ) :
    denote (diagonal f) = Matrix.diagonal (fun s => (f s:ℂ)) := by
  ext s t
  by_cases h : s = t <;> simp [denote,QuantumAlgebraicHistory.diagonal,h]

def distributed (c : QMACircuit) (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    QMACircuitTerm c → Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) Scalar
  | .inl i => diagonal (fun s =>
      if s (Sum.inl i.castSucc) = 0 ∧ s (Sum.inl i.succ) = 1 then 1 else 0)
  | .inr (.inl b) => if b = 0 then
      diagonal (fun s => if s (Sum.inl 0) = 1 then 0 else 1) else
      diagonal (fun s => if s (Sum.inl (Fin.last (c.gates.length+1))) = 0 then 0 else 1)
  | .inr (.inr (.inl i)) => diagonal (fun s =>
      if qmaClockAt c.gates.length (τ i) (s ∘ Sum.inl) ∧
        qmaInputCheck c i (s ∘ Sum.inr) then 14 else 0)
  | .inr (.inr (.inr (.inl _))) => diagonal (fun s =>
      if s (Sum.inl (qmaOutputMarker c)) = 1 ∧ s (Sum.inr (Fin.last c.work)) ≠ 1 then 1 else 0)
  | .inr (.inr (.inr (.inr t))) => fun s r =>
      mul (rat ((14*(c.work+1)+8)*c.gates.length:ℚ))
        (lift (qmaPropagationSites c t) (propagationCore c t) s r)

theorem denote_distributed (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    denote (distributed c τ a) = qmaDistributedTermMatrix c τ a := by
  rcases a with i | (b | (i | (u | t)))
  · ext s r
    simp only [distributed,denote,QuantumAlgebraicHistory.diagonal,qmaDistributedTermMatrix,qmaClockFaultTerm,
      qmaPairDiagonal,Matrix.diagonal_apply]
    split_ifs <;> simp
  · fin_cases b
    · change denote (QuantumAlgebraicHistory.diagonal
        (fun s : QMACircuitQubit c → Fin 2 => if s (Sum.inl 0) = 1 then 0 else 1)) =
        qmaClockLeftTerm c
      rw [denote_diagonal]
      ext s r
      simp only [qmaClockLeftTerm,qmaBitDiagonal,Matrix.diagonal_apply]
      split_ifs <;> norm_num
    · change denote (QuantumAlgebraicHistory.diagonal
        (fun s : QMACircuitQubit c → Fin 2 =>
          if s (Sum.inl (Fin.last (c.gates.length+1))) = 0 then 0 else 1)) =
        qmaClockRightTerm c
      rw [denote_diagonal]
      ext s r
      simp only [qmaClockRightTerm,qmaBitDiagonal,Matrix.diagonal_apply]
      split_ifs <;> norm_num
  · ext s r
    simp only [distributed,denote,QuantumAlgebraicHistory.diagonal,qmaDistributedTermMatrix,
      qmaDistributedInputTerm,Matrix.diagonal_apply]
    split_ifs <;> simp
  · cases u
    ext s r
    simp only [distributed,denote,QuantumAlgebraicHistory.diagonal,qmaDistributedTermMatrix,qmaOutputTerm,
      qmaPairDiagonal,Matrix.diagonal_apply]
    split_ifs <;> simp
  · change (fun s r => value (mul _ (lift _ _ s r))) = _
    simp only [value_mul,value_rat]
    have hl := denote_lift (qmaPropagationSites c t) (propagationCore c t)
    rw [denote_propagationCore] at hl
    have hc := (qmaLocalPropagationGram_local c t).core_lift
    rw [hc] at hl
    ext s r
    have he := congrFun (congrFun hl s) r
    dsimp only [denote] at he
    rw [he]
    simp only [qmaDistributedTermMatrix,Matrix.smul_apply,smul_eq_mul]
    push_cast
    rfl

def localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) : Scalar :=
  finiteProduct (fun k => if k = i then QuantumFixedPauli.pauli 2 (s k) (t k) else identity (s k) (t k))

theorem value_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    value (localY n i s t) = sourceLocalPauli n i 1 s t := by
  rw [localY,value_finiteProduct]
  unfold sourceLocalPauli sourceTensor
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = i
  · simp only [h,ite_true,value_pauli]
    rfl
  · simp only [h,ite_false,value_identity]

def rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) : Scalar :=
  add (mul (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))))
    (mul (neg imaginary) (mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
      (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))))

theorem denote_rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) :
    denote (rebit n i A) = qmaDistributedRebitOnQubits n i (denote A) := by
  rw [qmaDistributedRebitOnQubits_eq]
  ext s t
  simp only [denote,rebit,value_add,value_mul,value_identity,value_realPart,value_imagPart,
    value_neg,value_imaginary,value_localY,qmaJoinMatrix,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.submatrix_apply]
  rfl

def pairY (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) : Scalar :=
  mul (mul (QuantumFixedPauli.pauli 2 (s i) (t i)) (QuantumFixedPauli.pauli 2 (s j) (t j)))
    (rat (if ∀ k, k ≠ i → k ≠ j → s k = t k then 1 else 0))

theorem value_pairY (n : ℕ) (i j : Fin n) (hne : i ≠ j) (s t : SourceSpinBasis n) :
    value (pairY n i j s t) = (sourceLocalPauli n i 1*sourceLocalPauli n j 1) s t := by
  rw [sourceLocalPauli_product_entry n i j hne]
  simp only [pairY,value_mul,value_pauli]
  have he (a b : Fin 2) : qmaPauli 2 a b = ContinuumCoulomb.pauli 1 a b := rfl
  rw [he,he]
  by_cases h : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [ite_eq_left h,sourceSpectatorDelta_eq_one n i j s t h]
    simp
  · rw [ite_eq_right h,sourceSpectatorDelta_eq_zero n i j s t h]
    simp

def referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (s t : Fin (n+1) ⊕ ι → Fin 2) : Scalar :=
  mul (mul (rat (1/2)) (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl))))
    (identity (s ∘ Sum.inr) (t ∘ Sum.inr))

theorem denote_referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n) :
    denote (referenceEdge (ι := ι) n i) = qmaReferenceEdgeOnQubits (ι := ι) n i := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have he := congrArg Fin.val h
    simp at he
  ext s t
  simp only [denote,referenceEdge,value_mul,value_rat,value_sub,value_identity,
    value_pairY _ _ _ hne,qmaReferenceEdgeOnQubits,qmaJoinMatrix,qmaReferenceYEdge,
    Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.sub_apply]
  norm_num
  rfl

def orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length) :
    QMAReferenceTerm (qmaHistoryReferenceWork c) →
      Matrix (Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2)
        (Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2) Scalar
  | .inl i => rebit (qmaHistoryReferenceWork c+1) i
      (distributed c (qmaFirstUseTime c) (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i))
  | .inr i => referenceEdge (qmaHistoryReferenceWork c) i

theorem denote_orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    denote (orderedTerm c hT a) = (qmaOrderedHistoryModel c hT).matrix a := by
  cases a with
  | inl i =>
    rw [orderedTerm,denote_rebit,denote_distributed]
    rfl
  | inr i =>
    rw [orderedTerm,denote_referenceEdge]
    rfl

def orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Matrix (QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a))
      (QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a)) Scalar :=
  fun s t => orderedTerm c hT a (qmaSupportExtend _ s) (qmaSupportExtend _ t)

theorem denote_orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    denote (orderedCore c hT a) = qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
      ((qmaOrderedHistoryModel c hT).matrix a) := by
  ext s t
  exact congrFun (congrFun (denote_orderedTerm c hT a) _) _

theorem orderedCoefficient_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : {x // x ∈ (qmaOrderedHistoryModel c hT).sites a} → Fin 4) :
    realValue (realCoefficient (orderedCore c hT a) w) =
      (qmaPauliCoefficient (qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
        ((qmaOrderedHistoryModel c hT).matrix a)) w).re := by
  rw [realCoefficient_eq]
  change (qmaPauliCoefficient (denote (orderedCore c hT a)) w).re = _
  rw [denote_orderedCore]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
