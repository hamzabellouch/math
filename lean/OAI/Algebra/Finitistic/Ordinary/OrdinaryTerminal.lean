import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimodule

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- The terminal character extended along the B-factor. -/
def terminalAugmentation : (B ⊗[k] ChainAlgebra k l) →ₐ[k] B :=
  Algebra.TensorProduct.lift (AlgHom.id k B)
    ((Algebra.ofId k B).comp (ChainAlgebra.terminalCharacter k l)) (by
      intro b c
      change b * algebraMap k B (ChainAlgebra.terminalCharacter k l c) =
        algebraMap k B (ChainAlgebra.terminalCharacter k l c) * b
      exact (Algebra.commutes _ _).symm)

/-- Coordinate model for B tensor_k W, with its specified terminal right action. -/
def TerminalTensor := B
namespace TerminalTensor
instance : AddCommGroup (TerminalTensor B) := inferInstanceAs (AddCommGroup B)
instance : Module k (TerminalTensor B) := inferInstanceAs (Module k B)
instance : Module B (TerminalTensor B) := inferInstanceAs (Module B B)
instance : Module (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) :=
  Module.compHom B (terminalAugmentation k B l).toRingHom.op

def value (t : TerminalTensor B) : B := t

@[simp] theorem right_action (x : (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) (t : TerminalTensor B) :
    value B (x • t) = value B t * terminalAugmentation k B l x.unop := rfl

instance towerLeft : IsScalarTower k B (TerminalTensor B) := inferInstanceAs (IsScalarTower k B B)

instance towerRight : IsScalarTower k (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) where
  smul_assoc c x v := by
    change value B v * terminalAugmentation k B l (c • x.unop) = c • (value B v * terminalAugmentation k B l x.unop)
    rw [map_smul, mul_smul_comm]

instance commuteActions : SMulCommClass B (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) where
  smul_comm b x t := by
    change b * (value B t * terminalAugmentation k B l x.unop) =
      (b*value B t) * terminalAugmentation k B l x.unop
    exact (mul_assoc _ _ _).symm

/-- Explicit identification of this coordinate model with the source tensor product. -/
def tensorModel : (B ⊗[k] k) ≃ₗ[k] TerminalTensor B := TensorProduct.rid k B

@[simp] theorem tensorModel_tmul (b : B) (c : k) :
    tensorModel k B (b ⊗ₜ[k] c) = c • b := rfl

/-- The coordinate right action has exactly the regular-B/terminal-W tensor formula. -/
theorem tensor_right_formula (b b' : B) (w : k) (c : ChainAlgebra k l) :
    MulOpposite.op (b' ⊗ₜ[k] c) • tensorModel k B (b ⊗ₜ[k] w) =
      tensorModel k B ((b*b') ⊗ₜ[k] (w * ChainAlgebra.terminalCharacter k l c)) := by
  change (w • b) * (b' * algebraMap k B (ChainAlgebra.terminalCharacter k l c)) =
    (w * ChainAlgebra.terminalCharacter k l c) • (b*b')
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  have hc := Algebra.commutes (R := k) (A := B) (ChainAlgebra.terminalCharacter k l c) (b*b')
  calc
    _ = algebraMap k B w * ((b*b') * algebraMap k B (ChainAlgebra.terminalCharacter k l c)) := by simp only [mul_assoc]
    _ = _ := by rw [← hc]; simp only [mul_assoc]

instance finiteDimensional [FiniteDimensional k B] : FiniteDimensional k (TerminalTensor B) :=
  inferInstanceAs (FiniteDimensional k B)
end TerminalTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
