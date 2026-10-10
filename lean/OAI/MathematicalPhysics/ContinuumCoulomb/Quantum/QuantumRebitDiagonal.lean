import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDiagonal

namespace OAI

/-! A real diagonal term remains diagonal under the reference-spin rebit
construction.  These entry identities avoid any sum over spectators. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumAlgebraicHistory QuantumAlgebraicScalar
open scoped Classical

theorem rebit_rat_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=rat q) :
    rebit n i A s t = if s ∘ Sum.inl=t ∘ Sum.inl then rat q else rat 0 := by
  by_cases h : s ∘ Sum.inl=t ∘ Sum.inl
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]

theorem rebit_diagonal_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=
      if s ∘ Sum.inr=t ∘ Sum.inr then rat q else rat 0) :
    rebit n i A s t = if s=t then rat q else rat 0 := by
  by_cases hb : s ∘ Sum.inr=t ∘ Sum.inr
  · rw [ite_eq_left hb] at hA
    rw [rebit_rat_entry n i A s t q hA]
    have he : (s ∘ Sum.inl=t ∘ Sum.inl) ↔ s=t := by
      constructor
      · intro hr
        funext a
        cases a with
        | inl a => exact congrFun hr a
        | inr a => exact congrFun hb a
      · intro h
        exact congrArg (fun f => f ∘ Sum.inl) h
    simp only [he]
  · rw [ite_eq_right hb] at hA
    rw [rebit_rat_entry n i A s t 0 hA]
    have hne : s≠t := fun h => hb (congrArg (fun f => f ∘ Sum.inr) h)
    simp [hne]

def orderedExtend (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    QuantumOrderedSupport.Qubit c → Fin 2 :=
  qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
    (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j))

theorem orderedExtend_at (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (i : Fin (QuantumOrderedSupport.sites c hT a).length) :
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val)=s i := by
  calc
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val) =
      s ((QuantumOrderedSupport.supportEquiv c hT a).symm
        (QuantumOrderedSupport.supportEquiv c hT a i)) :=
      dite_eq_left (QuantumOrderedSupport.supportEquiv c hT a i).property
    _ = s i := congrArg s ((QuantumOrderedSupport.supportEquiv c hT a).symm_apply_apply i)

theorem orderedExtend_injective (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Function.Injective (orderedExtend c hT a) := by
  intro s t h
  funext i
  have he := congrFun h (QuantumOrderedSupport.supportEquiv c hT a i).val
  simpa only [orderedExtend_at] using he

theorem ordered_diagonal_entry (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (QuantumHistoryDescriptors.encode c
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4)
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    orderedTable c hT (.inl i) s t = if s=t then rat (weight c
      (QuantumHistoryDescriptors.encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i))
      (supportData c hT (.inl i) s t)) else rat 0 := by
  let S := orderedExtend c hT (.inl i) s
  let T := orderedExtend c hT (.inl i) t
  let a := qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i
  have hd := distributed_entry c a ha (supportData c hT (.inl i) s t)
  rw [readRow_actual,readColumn_actual] at hd
  have he := rebit_diagonal_entry (qmaHistoryReferenceWork c+1) i
    (distributed c (qmaFirstUseTime c) a) S T
    (weight c (QuantumHistoryDescriptors.encode c a) (supportData c hT (.inl i) s t)) hd
  have hs : S=T ↔ s=t := (orderedExtend_injective c hT (.inl i)).eq_iff
  change rebit (qmaHistoryReferenceWork c+1) i (distributed c (qmaFirstUseTime c) a) S T = _
  rw [he]
  simp only [hs]
  rfl

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
