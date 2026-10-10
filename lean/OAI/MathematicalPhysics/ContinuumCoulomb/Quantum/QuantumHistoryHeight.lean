import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCoefficient
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientHeight

namespace OAI

/-! Polynomial bounds for the actual rational-register history entries.
The only matrix multiplication takes place on the five-site propagation
core, with at most32 intermediate configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem height_identity {α : Type} [DecidableEq α] (s t : α) :
    height (identity s t) ≤ 1 := by
  by_cases h : s = t <;> simp [identity,h]

theorem height_hadamard (s t : Fin 2) : height (hadamard s t) ≤ 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [hadamard,mul,realMul,realSub,realAdd,realNeg,sqrtHalf,
      rat,realRat,height,realHeight]

theorem height_phaseT (s t : Fin 2) : height (phaseT s t) ≤ 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [phaseT,mul,realMul,realSub,realAdd,realNeg,QuantumAlgebraicScalar.add,sqrtHalf,
      rat,realRat,imaginary,height,realHeight]

private theorem height_single_product (n : ℕ) (i : Fin n)
    (A : Fin 2 → Fin 2 → Scalar) (hA : ∀ s t, height (A s t) ≤ 2)
    (s t : SourceSpinBasis n) :
    height (finiteProduct (fun k => if k = i then A (s k) (t k)
      else identity (s k) (t k))) ≤ 2 := by
  apply (height_finiteProduct _).trans
  calc
    _ ≤ ∏ k : Fin n, if k = i then (2:ℚ) else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => height_nonnegative _)
      intro k _
      by_cases h : k = i
      · simpa only [h,ite_true] using hA (s k) (t k)
      · simpa only [h,ite_false] using height_identity (s k) (t k)
    _ = 2 := by simp

theorem height_gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) :
    height (gate work g s t) ≤ 2 := by
  cases g with
  | hadamard i => exact height_single_product _ _ _ height_hadamard s t
  | phaseT i => exact height_single_product _ _ _ height_phaseT s t
  | controlledNot i j =>
    dsimp only [gate]
    split_ifs <;> norm_num

theorem height_delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) : height (delta c t s r) ≤ 3 := by
  dsimp only [delta]
  split_ifs
  · apply (height_sub _ _).trans
    have hm := height_mul
      (identity (s ∘ Sum.inl) (r ∘ Sum.inl))
      (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr))
    have hi := height_identity s (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) r)
    have hj := height_identity (s ∘ Sum.inl) (r ∘ Sum.inl)
    have hg := height_gate c.work (c.gates.getD t.val (.hadamard 0))
      (s ∘ Sum.inr) (r ∘ Sum.inr)
    have hn := height_nonnegative
      (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr))
    nlinarith
  · norm_num

theorem propagation_configurations (c : QMACircuit) (t : Fin c.gates.length) :
    Fintype.card (QMASupportBasis (qmaPropagationSites c t)) ≤ 32 := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (qmaPropagationSites_card c t)
  simpa only [QMASupportBasis,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,
    show (2:ℕ)^5 = 32 by norm_num] using h

theorem height_propagationCore (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMASupportBasis (qmaPropagationSites c t)) :
    height (propagationCore c t s r) ≤ 288 := by
  have hentry (u : QMASupportBasis (qmaPropagationSites c t)) :
      height (mul (adjoint (deltaCore c t) s u) (deltaCore c t u r)) ≤ 9 := by
    apply (height_mul _ _).trans
    simp only [adjoint,height_conj,deltaCore]
    calc
      _ ≤ (3:ℚ)*3 := mul_le_mul (height_delta c t _ _) (height_delta c t _ _)
        (height_nonnegative _) (by norm_num)
      _ = 9 := by norm_num
  have hsum := (height_finiteSum (fun u =>
    mul (adjoint (deltaCore c t) s u) (deltaCore c t u r))).trans
      (Finset.sum_le_sum (fun u _ => hentry u))
  have hcard : (Fintype.card (QMASupportBasis (qmaPropagationSites c t)):ℚ) ≤ 32 :=
    Nat.cast_le.mpr (propagation_configurations c t)
  change height (finiteSum _) ≤ 288
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  linarith

theorem height_lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (s t : ι → Fin 2) :
    height (lift S A s t) ≤ height (A (fun i => s i.val) (fun i => t i.val)) := by
  apply (height_mul _ _).trans
  simpa using mul_le_mul_of_nonneg_left
    (height_identity (fun i : {i // i ∉ S} => s i.val) (fun i => t i.val))
    (height_nonnegative (A (fun i => s i.val) (fun i => t i.val)))

def historyHeight (c : QMACircuit) : ℚ :=
  14+288*((14*(c.work+1)+8)*c.gates.length)

theorem historyHeight_nonnegative (c : QMACircuit) : 0 ≤ historyHeight c := by
  unfold historyHeight
  positivity

theorem height_distributed (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c)
    (s r : QMACircuitQubit c → Fin 2) :
    height (distributed c τ a s r) ≤ historyHeight c := by
  have h14 : (14:ℚ) ≤ historyHeight c := by
    unfold historyHeight
    have hn : 0 ≤ 288*((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
    linarith
  rcases a with i | (b | (i | (u | t)))
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · by_cases hb : b = 0
    · simp only [distributed,hb,ite_true,QuantumAlgebraicHistory.diagonal]
      split_ifs <;> norm_num <;> linarith
    · simp only [distributed,hb,ite_false,QuantumAlgebraicHistory.diagonal]
      split_ifs <;> norm_num <;> linarith
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · apply (height_mul _ _).trans
    have hl := (height_lift _ (propagationCore c t) s r).trans
      (height_propagationCore c t _ _)
    have hw : 0 ≤ ((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
    rw [height_rat,abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_left hl hw).trans
    unfold historyHeight
    linarith

theorem height_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    height (localY n i s t) ≤ 1 := by
  apply (height_finiteProduct _).trans
  apply Finset.prod_le_one₀ (fun _ _ => height_nonnegative _)
  intro k _
  by_cases h : k = i
  · simpa only [h,ite_true] using height_pauli 2 (s k) (t k)
  · simpa only [h,ite_false] using height_identity (s k) (t k)

theorem height_rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (s t : Fin n ⊕ ι → Fin 2) :
    height (rebit n i A s t) ≤ 2*height (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  have hI := height_identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hY := height_localY n i (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hR := height_realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))
  have hJ := height_imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))
  have hYR := height_mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
    (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))
  have hIR := height_mul (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
    (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))
  have hN := height_mul (neg imaginary)
    (mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
      (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))))
  simp only [height_neg,height_imaginary,one_mul] at hN
  apply (height_add _ _).trans
  nlinarith [height_nonnegative (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))),
    height_nonnegative (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))]

theorem height_pairY (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) :
    height (pairY n i j s t) ≤ 1 := by
  have hp := (height_mul (QuantumFixedPauli.pauli 2 (s i) (t i)) (QuantumFixedPauli.pauli 2 (s j) (t j))).trans
    (mul_le_mul (height_pauli 2 (s i) (t i)) (height_pauli 2 (s j) (t j))
      (height_nonnegative _) (by norm_num))
  have hδ : height (rat (if ∀ k, k ≠ i → k ≠ j → s k = t k then 1 else 0)) ≤ 1 := by
    split_ifs <;> norm_num
  apply (height_mul _ _).trans
  simpa using mul_le_mul hp hδ (height_nonnegative _) (by norm_num)

theorem height_referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (s t : Fin (n+1) ⊕ ι → Fin 2) :
    height (referenceEdge n i s t) ≤ 1 := by
  have hI := height_identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hY := height_pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hS := height_sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
    (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl))
  have hhalf := height_mul (rat (1/2))
    (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)))
  norm_num only [height_rat,abs_of_pos (by norm_num : (0:ℚ) < 1/2)] at hhalf
  have hB : height (mul (rat (1/2))
      (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
        (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)))) ≤ 1 := by
    linarith
  apply (height_mul _ _).trans
  simpa using mul_le_mul hB (height_identity (s ∘ Sum.inr) (t ∘ Sum.inr))
    (height_nonnegative _) (by norm_num)

theorem height_orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2) :
    height (orderedTerm c hT a s t) ≤ 2*historyHeight c := by
  cases a with
  | inl i =>
    exact (height_rebit _ _ _ s t).trans
      (mul_le_mul_of_nonneg_left (height_distributed c _ _ _ _) (by norm_num))
  | inr i =>
    apply (height_referenceEdge _ _ s t).trans
    have h : (14:ℚ) ≤ historyHeight c := by
      unfold historyHeight
      have hn : 0 ≤ 288*((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
      linarith
    linarith

theorem height_orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a)) :
    height (orderedCore c hT a s t) ≤ 2*historyHeight c :=
  height_orderedTerm c hT a _ _

theorem orderedCoefficient_height (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : {x // x ∈ (qmaOrderedHistoryModel c hT).sites a} → Fin 4) :
    realHeight (realCoefficient (orderedCore c hT a) w) ≤ 128*historyHeight c := by
  have hp : (2:ℚ)^Fintype.card {x // x ∈ (qmaOrderedHistoryModel c hT).sites a} ≤ 64 := by
    have hc := (qmaOrderedHistoryModel c hT).card a
    rw [Fintype.card_coe]
    have hb := pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hc
    norm_num at hb ⊢
    exact hb
  calc
    _ ≤ (2:ℚ)^Fintype.card {x // x ∈ (qmaOrderedHistoryModel c hT).sites a}*
        (2*historyHeight c) :=
      realHeight_coefficient _ _ _ (height_orderedCore c hT a)
    _ ≤ 64*(2*historyHeight c) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    _ = _ := by ring

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
