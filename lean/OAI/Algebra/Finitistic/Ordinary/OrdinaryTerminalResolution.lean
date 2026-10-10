import OAI.Algebra.Finitistic.Ordinary.OrdinaryChainResolution

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- W is the genuine terminal right simple, via the terminal character. -/
def TerminalSimple := k
namespace TerminalSimple
instance : AddCommGroup (TerminalSimple k) := inferInstanceAs (AddCommGroup k)
instance : Module k (TerminalSimple k) := inferInstanceAs (Module k k)
instance : Module (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k) :=
  Module.compHom k (ChainAlgebra.terminalCharacter k l).toRingHom.op
end TerminalSimple

namespace ChainAlgebra
/-- The augmentation of the terminal right projective. -/
def augmentation : rightTerm (k := k) (Fin.last l) →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] TerminalSimple k where
  toFun x := x.val.1 (Fin.last l)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem augmentation_zero_iff (x : rightTerm (k := k) (Fin.last l)) :
    augmentation k l x = 0 ↔ x.val.1 (Fin.last l) = 0 := Iff.rfl

theorem augmentation_surjective : Function.Surjective (augmentation k l) := by
  intro w
  let x : rightTerm (k := k) (Fin.last l) := ⟨(show k from w) • vertex k l (Fin.last l), by
    change vertex k l (Fin.last l) * ((show k from w) • vertex k l (Fin.last l)) =
      (show k from w) • vertex k l (Fin.last l)
    rw [mul_smul_comm, vertex_idempotent]⟩
  refine ⟨x, ?_⟩
  change ((show k from w) • vertex k l (Fin.last l)).1 (Fin.last l) = (show k from w)
  rw [smul_diagonal, vertex_diagonal]
  simp only [Pi.single_eq_same]
  exact @mul_one k _ w

/-- Exactness at the augmentation for every positive chain length. -/
theorem augmentation_exact (x : rightTerm (k := k) (Fin.last (l+1))) :
    augmentation k (l+1) x = 0 ↔
      ∃ y, resolutionMap (k := k) (Fin.last l) y = x := by
  rw [augmentation_zero_iff, resolutionMap_range]
  rfl

theorem augmentation_zero_injective : Function.Injective (augmentation k 0) := by
  intro x y hxy
  have hz : (x-y).val.1 0 = 0 := by
    have hz : augmentation k 0 (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    exact (augmentation_zero_iff k 0 _).mp hz
  have he := vertex_zero_mul (x-y).val
  have hp : vertex k 0 0 * (x-y).val = (x-y).val := (x-y).property
  rw [hp, hz, zero_smul] at he
  exact sub_eq_zero.mp (show x-y = 0 from Subtype.ext he)

/-- For l=0, the source resolution is the actual isomorphism e₀C ≅ W. -/
def zeroLengthResolution : rightTerm (k := k) (Fin.last 0) ≃ₗ[(ChainAlgebra k 0)ᵐᵒᵖ] TerminalSimple k :=
  LinearEquiv.ofBijective (augmentation k 0) ⟨augmentation_zero_injective k, augmentation_surjective k 0⟩
end ChainAlgebra
end LittleFinitistic.OrdinarySimulation

end

end OAI
