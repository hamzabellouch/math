import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAdjacentCnot

namespace OAI

/-! Replacing a gate by an exact bounded-length nearest-neighbor gate sequence. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def QMAGate.Adjacent : QMAGate → Prop
  | .controlledNot i j => i+1 = j ∨ j+1 = i
  | _ => True

theorem qmaAdjacentCnot_valid (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    ∀ g ∈ qmaAdjacentCnot work a d h b, g.WellFormed (work+1) ∧ g.Adjacent := by
  induction d generalizing a with
  | zero =>
    intro g hg
    have he : g = qmaOrderedCnot a (a+1) b := by simpa [qmaAdjacentCnot] using hg
    subst g
    cases b <;> simp only [qmaOrderedCnot,Bool.false_eq_true,ite_false,ite_true,
      QMAGate.WellFormed,QMAGate.Adjacent]
    · exact ⟨⟨h,by omega,by omega⟩,by simp⟩
    · exact ⟨⟨by omega,h,by omega⟩,by simp⟩
  | succ d ih =>
    intro g hg
    simp only [qmaAdjacentCnot,List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · have hs : g.WellFormed (work+1) := qmaWireSwapGates_wellFormed
        (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩ (by intro he; cases he) g hg
      refine ⟨hs,?_⟩
      simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp [QMAGate.Adjacent]
    · exact ih (a+1) (by omega) g hg
    · have hs : g.WellFormed (work+1) := qmaWireSwapGates_wellFormed
        (⟨a,by omega⟩ : Fin (work+1)) ⟨a+1,by omega⟩ (by intro he; cases he) g hg
      refine ⟨hs,?_⟩
      simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp [QMAGate.Adjacent]

def qmaNearestGate (work : ℕ) : QMAGate → List QMAGate
  | .controlledNot i j =>
      if h : i < j ∧ j < work+1 then
        qmaAdjacentCnot work i (j-i-1) (by omega) true
      else if h : j < i ∧ i < work+1 then
        qmaAdjacentCnot work j (i-j-1) (by omega) false
      else [.controlledNot i j]
  | g => [g]

theorem qmaNearestGate_matrix (work : ℕ) (g : QMAGate) :
    qmaGateProduct work (qmaNearestGate work g) = qmaGateMatrix work g := by
  cases g with
  | hadamard i => exact qmaGateProduct_singleton _ _
  | phaseT i => exact qmaGateProduct_singleton _ _
  | controlledNot i j =>
    by_cases h : i < j ∧ j < work+1
    · simp only [qmaNearestGate,dite_eq_left h,qmaAdjacentCnot_matrix,qmaOrderedCnot,ite_true]
      have he : i+(j-i-1)+1 = j := by omega
      rw [he]
    · by_cases h' : j < i ∧ i < work+1
      · simp only [qmaNearestGate,dite_eq_right h,dite_eq_left h',qmaAdjacentCnot_matrix,
          qmaOrderedCnot,Bool.false_eq_true,ite_false]
        have he : j+(i-j-1)+1 = i := by omega
        rw [he]
      · simp only [qmaNearestGate,dite_eq_right h,dite_eq_right h',qmaGateProduct_singleton]

theorem qmaNearestGate_valid (work : ℕ) (g : QMAGate) (hg : g.WellFormed (work+1)) :
    ∀ k ∈ qmaNearestGate work g, k.WellFormed (work+1) ∧ k.Adjacent := by
  cases g with
  | hadamard i => simpa [qmaNearestGate,QMAGate.Adjacent] using hg
  | phaseT i => simpa [qmaNearestGate,QMAGate.Adjacent] using hg
  | controlledNot i j =>
    rcases hg with ⟨hi,hj,hne⟩
    by_cases h : i < j ∧ j < work+1
    · simp only [qmaNearestGate,dite_eq_left h]
      exact qmaAdjacentCnot_valid _ _ _ _ _
    · have h' : j < i ∧ i < work+1 := by omega
      simp only [qmaNearestGate,dite_eq_right h,dite_eq_left h']
      exact qmaAdjacentCnot_valid _ _ _ _ _

theorem qmaNearestGate_length (work : ℕ) (g : QMAGate) :
    (qmaNearestGate work g).length ≤ 6*work+7 := by
  cases g with
  | hadamard i => simp [qmaNearestGate]
  | phaseT i => simp [qmaNearestGate]
  | controlledNot i j =>
    by_cases h : i < j ∧ j < work+1
    · simp only [qmaNearestGate,dite_eq_left h,qmaAdjacentCnot_length]
      omega
    · by_cases h' : j < i ∧ i < work+1
      · simp only [qmaNearestGate,dite_eq_right h,dite_eq_left h',qmaAdjacentCnot_length]
        omega
      · simp only [qmaNearestGate,dite_eq_right h,dite_eq_right h',List.length_singleton]
        omega

end ContinuumCoulomb

end

end OAI
