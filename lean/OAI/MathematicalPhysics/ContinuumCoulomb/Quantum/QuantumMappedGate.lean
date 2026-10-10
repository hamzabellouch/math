import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireRouting

namespace OAI

/-! Explicit gate addresses for a logical register embedded in a larger wire grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaMapGate (sourceWork targetWork : ℕ) (f : Fin (sourceWork+1) → Fin (targetWork+1)) :
    QMAGate → QMAGate
  | .hadamard i => .hadamard (f (qmaQubit sourceWork i)).val
  | .phaseT i => .phaseT (f (qmaQubit sourceWork i)).val
  | .controlledNot i j =>
      .controlledNot (f (qmaQubit sourceWork i)).val (f (qmaQubit sourceWork j)).val

theorem qmaMapGate_wellFormed (sourceWork targetWork : ℕ)
    (f : Fin (sourceWork+1) → Fin (targetWork+1)) (hf : Function.Injective f)
    (g : QMAGate) (hg : g.WellFormed (sourceWork+1)) :
    (qmaMapGate sourceWork targetWork f g).WellFormed (targetWork+1) := by
  cases g with
  | hadamard i => exact (f (qmaQubit sourceWork i)).isLt
  | phaseT i => exact (f (qmaQubit sourceWork i)).isLt
  | controlledNot i j =>
    refine ⟨(f (qmaQubit sourceWork i)).isLt,(f (qmaQubit sourceWork j)).isLt,?_⟩
    intro he
    have h := congrArg Fin.val (hf (Fin.ext he))
    simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1] at h
    exact hg.2.2 h

theorem qmaRelabelGate_map (sourceWork targetWork : ℕ)
    (f : Fin (sourceWork+1) → Fin (targetWork+1))
    (σ : Equiv.Perm (Fin (targetWork+1))) (g : QMAGate) :
    qmaRelabelGate targetWork σ (qmaMapGate sourceWork targetWork f g) =
      qmaMapGate sourceWork targetWork (σ ∘ f) g := by
  cases g <;> simp only [qmaMapGate,qmaRelabelGate,qmaQubit_fin,Function.comp_apply]

theorem qmaMapGate_congr (sourceWork targetWork : ℕ)
    (f h : Fin (sourceWork+1) → Fin (targetWork+1)) (he : ∀ i, f i = h i) (g : QMAGate) :
    qmaMapGate sourceWork targetWork f g = qmaMapGate sourceWork targetWork h g := by
  have hf : f = h := funext he
  rw [hf]

end ContinuumCoulomb

end

end OAI
