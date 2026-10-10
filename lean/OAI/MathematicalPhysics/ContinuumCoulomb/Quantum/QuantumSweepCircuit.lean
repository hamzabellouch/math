import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRowStageBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumNearestCircuit
import Mathlib.Data.Fin.Rev

namespace OAI

/-! Alternating row sweeps with gates inserted at the arrival of their operands. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaSweepOrder (width row : ℕ) : Equiv.Perm (Fin (width+1)) :=
  if row % 2 = 0 then Equiv.refl _ else Fin.revPerm

def qmaSweepCircuitFrom (rows width : ℕ) :
    (start : ℕ) → (gs : List QMAGate) → start+gs.length ≤ rows → List QMAGate
  | _,[],_ => []
  | start,g::gs,h =>
      qmaRowStage width (qmaGridWork rows width)
        (qmaGridQubit rows width ⟨start,by simp only [List.length_cons] at h; omega⟩)
        (qmaGridQubit rows width ⟨start+1,by simp only [List.length_cons] at h; omega⟩)
        (qmaSweepOrder width (rows-1-start)) g ++
      qmaSweepCircuitFrom rows width (start+1) gs (by simp only [List.length_cons] at h; omega)

theorem qmaSweepCircuitFrom_length (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaSweepCircuitFrom rows width start gs h).length = (3*(width+1)+1)*gs.length := by
  induction gs generalizing start with
  | nil => simp [qmaSweepCircuitFrom]
  | cons g gs ih =>
    simp only [qmaSweepCircuitFrom,List.length_append,qmaRowStage_length,ih,List.length_cons]
    ring

theorem qmaSweepCircuitFrom_matrix (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hg : ∀ g ∈ gs, g.WellFormed (width+1)) :
    qmaGateProduct (qmaGridWork rows width) (qmaSweepCircuitFrom rows width start gs h) =
      qmaGateProduct (qmaGridWork rows width) (qmaGridCircuitFrom rows width start gs h) := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    simp only [qmaSweepCircuitFrom,qmaGridCircuitFrom,qmaGateProduct_append,
      qmaGateProduct_singleton]
    rw [ih (start+1) ht (fun k hk => hg k (by simp [hk]))]
    have hstage := qmaRowStage_matrix width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaGridRow_injective rows width _) (qmaGridRow_injective rows width _)
      (qmaGridRows_disjoint rows width _ _ (by intro he; have := congrArg Fin.val he; simp at this))
      (qmaSweepOrder width (rows-1-start)) g (hg g (by simp))
    rw [hstage]
    rfl

theorem qmaSweepCircuitFrom_wellFormed (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hg : ∀ g ∈ gs, g.WellFormed (width+1)) :
    ∀ g ∈ qmaSweepCircuitFrom rows width start gs h,
      g.WellFormed (qmaGridWork rows width+1) := by
  induction gs generalizing start with
  | nil => simp [qmaSweepCircuitFrom]
  | cons g gs ih =>
    intro k hk
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    rcases List.mem_append.mp hk with hk | hk
    · exact qmaRowStage_wellFormed _ _ _ _ (qmaGridRow_injective rows width _)
        (qmaGridRows_disjoint rows width _ _ (qmaGridRow_ne rows ⟨start,hs⟩))
        _ g (hg g (by simp)) k hk
    · exact ih (start+1) ht (fun k hk => hg k (by simp [hk])) k hk

abbrev qmaSweepCircuit (c : QMACircuit) : QMACircuit :=
  ⟨qmaGridWork c.gates.length c.work,c.witness,
    qmaSweepCircuitFrom c.gates.length c.work 0 c.gates (by omega)⟩

theorem qmaSweepCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaSweepCircuit c).WellFormed := by
  exact ⟨hc.1.trans (Nat.le_add_right _ _),qmaSweepCircuitFrom_wellFormed _ _ _ _ _ hc.2⟩

theorem qmaSweepCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaSweepCircuit c) (qmaSweepCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  have hm : qmaCircuitMatrix (qmaSweepCircuit c) = qmaCircuitMatrix (qmaGridCircuit c) :=
    qmaSweepCircuitFrom_matrix _ _ _ _ _ hc.2
  calc
    _ = qmaAcceptance (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi := by
      unfold qmaAcceptance
      rw [hm]
      rfl
    _ = _ := qmaGridCircuit_acceptance c hc psi

end ContinuumCoulomb

end

end OAI
