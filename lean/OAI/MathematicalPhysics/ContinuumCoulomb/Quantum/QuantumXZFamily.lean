import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZReduction

namespace OAI

/-! Finite X/Z word families with their actual normalized ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaNormalizedBottom_instances {σ : Type*} (F G : Fintype σ)
    (d e : DecidableEq σ) (A : Matrix σ σ ℂ) :
    @MediatorGraph.normalizedBottom σ F d A = @MediatorGraph.normalizedBottom σ G e A := by
  cases Subsingleton.elim F G
  cases Subsingleton.elim d e
  rfl

structure QMAXZModel where
  Q : Type
  Term : Type
  [qFinite : Fintype Q]
  [qDecidable : DecidableEq Q]
  [termFinite : Fintype Term]
  word : Term → Q → Fin 4
  coefficient : Term → ℝ
  noY : ∀ e i, word e i ≠ 2
  card : ∀ e, (qmaPauliSupport (word e)).card ≤ 2

attribute [instance] QMAXZModel.qFinite QMAXZModel.qDecidable QMAXZModel.termFinite

def QMAXZModel.energy (M : QMAXZModel) : ℝ :=
  MediatorGraph.normalizedBottom (∑ e, (M.coefficient e:ℂ) • qmaPauliWord (M.word e))

def QMAXZModel.qubits (M : QMAXZModel) : ℕ := Fintype.card M.Q

def QMAXZModel.terms (M : QMAXZModel) : ℕ := Fintype.card M.Term

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]

def QMAXZModel.ofWords (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hy : ∀ e i, w e i ≠ 2) (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2) : QMAXZModel where
  Q := ι
  Term := κ
  qFinite := inferInstance
  qDecidable := inferInstance
  termFinite := inferInstance
  word := w
  coefficient := J
  noY := hy
  card := hw

theorem QMAXZModel.ofWords_energy (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hy : ∀ e i, w e i ≠ 2) (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2) :
    (QMAXZModel.ofWords w J hy hw).energy =
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e)) := rfl

theorem QMAXZModel.ofWords_qubits (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hy : ∀ e i, w e i ≠ 2) (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2) :
    (QMAXZModel.ofWords w J hy hw).qubits = Fintype.card ι := rfl

theorem QMAXZModel.ofWords_terms (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hy : ∀ e i, w e i ≠ 2) (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2) :
    (QMAXZModel.ofWords w J hy hw).terms = Fintype.card κ := rfl

end ContinuumCoulomb

end

end OAI
