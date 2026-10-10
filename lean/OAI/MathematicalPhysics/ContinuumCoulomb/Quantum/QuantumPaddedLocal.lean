import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedPauli
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedTable

namespace OAI

/-! Exact full-space meaning of a fixed-width local coefficient table.
The coordinate map is the order of the literal support list; padding only
duplicates local words and never introduces spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLocal
open scoped BigOperators Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def reindex {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ :=
  fun s t => A (fun i => s (e i)) (fun i => t (e i))

def word {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S}) (m : ℕ)
    (w : Fin (n+m) → Fin 4) : ι → Fin 4 :=
  qmaPauliExtend S (fun i => QuantumPaddedPauli.paddedWord n m w (e.symm i))

theorem word_support {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) : qmaPauliSupport (word S e m w) ⊆ S :=
  qmaPauliExtend_support _ _

theorem yCount_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (v : β → Fin 4) :
    qmaPauliYCount (fun i => v (e i)) = qmaPauliYCount v := by
  unfold qmaPauliYCount
  refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
  · intro i hi
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.apply_symm_apply] using hj

theorem word_even {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) : Even (qmaPauliYCount (word S e m w)) := by
  rw [word,qmaPauliExtend_yCount,yCount_reindex e.symm]
  exact QuantumPaddedPauli.paddedWord_even n m w

omit [Fintype ι] in
theorem local_word {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (v : Fin n → Fin 4) :
    qmaPauliWord (fun i => v (e.symm i)) = reindex S e (qmaPauliWord v) := by
  ext s t
  simpa only [reindex,Equiv.symm_symm] using
    QuantumAlgebraicHistory.pauliWord_reindex e.symm v s t

omit [Fintype ι] in
theorem local_expansion {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : Fin (n+m) → Fin 4,
      (QuantumPaddedPauli.paddedCoefficient n m A w:ℂ) •
        qmaPauliWord (fun i => QuantumPaddedPauli.paddedWord n m w (e.symm i))) =
      reindex S e A := by
  simp only [local_word]
  ext s t
  have h := congrFun (congrFun (QuantumPaddedPauli.padded_expansion n m A hH hR)
    (fun i => s (e i))) (fun i => t (e i))
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,reindex] using h

theorem full_expansion {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : Fin (n+m) → Fin 4,
      (QuantumPaddedPauli.paddedCoefficient n m A w:ℂ) • qmaPauliWord (word S e m w)) =
      qmaLocalLift S (reindex S e A) := by
  simp only [word,qmaPauliExtend_lift,← qmaLocalLift_smul,← qmaLocalLift_sum]
  rw [local_expansion S e m A hH hR]

end ContinuumCoulomb.QuantumPaddedLocal

end

end OAI
