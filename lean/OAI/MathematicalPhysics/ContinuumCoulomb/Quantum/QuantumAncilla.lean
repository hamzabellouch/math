import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvolution

namespace OAI

/-! Exact witness embedding into the zero-ancilla subspace. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def QMAAncillaZero (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) : Prop :=
  ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0

def qmaWitnessRestrict (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis (c.work+1)) : SourceSpinBasis c.witness :=
  fun i => s ⟨i.val,lt_of_lt_of_le i.isLt (hc.1.trans (Nat.le_succ _))⟩

def qmaWitnessExtend (c : QMACircuit) (s : SourceSpinBasis c.witness) :
    SourceSpinBasis (c.work+1) :=
  fun i => if h : i.val < c.witness then s ⟨i.val,h⟩ else 0

theorem qmaWitnessExtend_ancilla (c : QMACircuit) (s : SourceSpinBasis c.witness) :
    QMAAncillaZero c (qmaWitnessExtend c s) := by
  intro i hi
  simp [qmaWitnessExtend,not_lt.mpr hi]

theorem qmaWitnessRestrict_extend (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis c.witness) :
    qmaWitnessRestrict c hc (qmaWitnessExtend c s) = s := by
  funext i
  simp [qmaWitnessRestrict,qmaWitnessExtend,i.isLt]

theorem qmaWitnessExtend_restrict (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis (c.work+1)) (hs : QMAAncillaZero c s) :
    qmaWitnessExtend c (qmaWitnessRestrict c hc s) = s := by
  funext i
  by_cases hi : i.val < c.witness
  · simp [qmaWitnessExtend,qmaWitnessRestrict,hi]
  · simp [qmaWitnessExtend,hi,hs i (Nat.le_of_not_gt hi)]

def qmaZeroAncillaEquiv (c : QMACircuit) (hc : c.WellFormed) :
    {s : SourceSpinBasis (c.work+1) // QMAAncillaZero c s} ≃ SourceSpinBasis c.witness where
  toFun s := qmaWitnessRestrict c hc s.val
  invFun s := ⟨qmaWitnessExtend c s,qmaWitnessExtend_ancilla c s⟩
  left_inv s := Subtype.ext (qmaWitnessExtend_restrict c hc s.val s.property)
  right_inv := qmaWitnessRestrict_extend c hc

theorem qmaInitialState_mass (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    sourceSpinMass (qmaInitialState c hc psi) = ‖psi‖^2 := by
  classical
  have he := (qmaZeroAncillaEquiv c hc).sum_comp (fun s => Complex.normSq (psi s))
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rw [←he]
  have hp (s : SourceSpinBasis (c.work+1)) :
      Complex.normSq (qmaInitialState c hc psi s) = if QMAAncillaZero c s then
        Complex.normSq (psi (qmaWitnessRestrict c hc s)) else 0 := by
    by_cases hs : QMAAncillaZero c s
    · have hs' : ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
      simp only [qmaInitialState,ite_eq_left hs',ite_eq_left hs]
      rfl
    · have hs' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
      simp only [qmaInitialState,ite_eq_right hs',ite_eq_right hs,Complex.normSq_zero]
  unfold sourceSpinMass
  simp_rw [hp]
  have hsub := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (QMAAncillaZero c))
    (by simp : ∀ s, s ∈ Finset.univ.filter (QMAAncillaZero c) ↔ QMAAncillaZero c s)
    (fun s => Complex.normSq (psi (qmaWitnessRestrict c hc s)))
  rw [Finset.sum_filter] at hsub
  exact hsub

end ContinuumCoulomb

end

end OAI
