import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTimeGrouping

namespace OAI

/-! Assign every actual history term to its clock time and enumerate by time. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaBoundedClockTime (T : ℕ) (hT : 0 < T) (n : ℕ) : Fin T :=
  ⟨min n (T-1),by omega⟩

theorem qmaBoundedClockTime_eq (T : ℕ) (hT : 0 < T) (n : Fin T) :
    qmaBoundedClockTime T hT n.val = n := by
  apply Fin.ext
  simp only [qmaBoundedClockTime]
  exact min_eq_left (by omega)

def qmaHistoryTermTime (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : QMACircuitTerm c → Fin c.gates.length
  | .inl i => qmaBoundedClockTime _ hT i.val
  | .inr (.inl b) => if b = 0 then ⟨0,hT⟩ else qmaBoundedClockTime _ hT c.gates.length
  | .inr (.inr (.inl i)) => qmaBoundedClockTime _ hT (τ i).val
  | .inr (.inr (.inr (.inl _))) => qmaBoundedClockTime _ hT c.gates.length
  | .inr (.inr (.inr (.inr t))) => t

def qmaHistoryTermList (c : QMACircuit) : List (QMACircuitTerm c) :=
  List.ofFn (qmaHistoryTermIndex c).symm

theorem qmaHistoryTermList_mem (c : QMACircuit) (a : QMACircuitTerm c) :
    a ∈ qmaHistoryTermList c := by
  apply List.mem_ofFn.mpr
  exact ⟨qmaHistoryTermIndex c a,(qmaHistoryTermIndex c).symm_apply_apply a⟩

theorem qmaHistoryTermList_nodup (c : QMACircuit) : (qmaHistoryTermList c).Nodup :=
  List.nodup_ofFn.mpr (qmaHistoryTermIndex c).symm.injective

def qmaOrderedHistoryTerms (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : List (QMACircuitTerm c) :=
  qmaGroupByTime c.gates.length (qmaHistoryTermTime c hT τ) (qmaHistoryTermList c)

theorem qmaOrderedHistoryTerms_mem (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    a ∈ qmaOrderedHistoryTerms c hT τ :=
  (qmaGroupByTime_perm _ _ _).mem_iff.mpr (qmaHistoryTermList_mem c a)

theorem qmaOrderedHistoryTerms_nodup (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaOrderedHistoryTerms c hT τ).Nodup :=
  qmaGroupByTime_nodup _ _ _ (qmaHistoryTermList_nodup c)

theorem qmaOrderedHistoryTerms_length (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaOrderedHistoryTerms c hT τ).length = qmaHistoryReferenceWork c+1 := by
  rw [qmaOrderedHistoryTerms,qmaGroupByTime_length]
  exact List.length_ofFn

theorem qmaOrderedHistoryTerms_sorted (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaOrderedHistoryTerms c hT τ).Pairwise
      (fun a b => qmaHistoryTermTime c hT τ a ≤ qmaHistoryTermTime c hT τ b) :=
  qmaGroupByTime_sorted _ _ _

end ContinuumCoulomb

end

end OAI
