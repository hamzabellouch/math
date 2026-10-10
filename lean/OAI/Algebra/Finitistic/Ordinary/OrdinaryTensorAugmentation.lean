import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorResolution
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTerminal

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

instance TerminalSimple.tower : IsScalarTower k (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k) where
  smul_assoc r x w := by
    change (show k from w) * (r * (ChainAlgebra.terminalCharacter k l x.unop)) =
      r * ((show k from w) * ChainAlgebra.terminalCharacter k l x.unop)
    ring

namespace TensorResolution
open ChainAlgebra

def simpleCoordinates : TerminalSimple k ≃ₗ[k] k where
  toFun w := w
  invFun w := w
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def terminalEquiv : B ⊗[k] TerminalSimple k ≃ₗ[k] TerminalTensor B :=
  (TensorProduct.congr (LinearEquiv.refl k B) (simpleCoordinates k)).trans (TerminalTensor.tensorModel k B)

/-- The augmentation retains the actual right BC-action. -/
def augmentation : term k B l l →ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ] TerminalTensor B where
  toFun x := terminalAugmentation k B l x.val
  map_add' x y := map_add _ x.val y.val
  map_smul' r x := map_mul (terminalAugmentation k B l) x.val r.unop

/-- The ordinary augmentation is exactly B tensor the terminal C-augmentation. -/
theorem augmentation_tensor (z : B ⊗[k] resolutionIdeal k l l) :
    augmentation k B l (termEquiv k B l l z) =
      terminalEquiv k B (((resolutionAugmentation k l).hom.restrictScalars k).lTensor B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    change b * algebraMap k B (c.val.1 (Fin.last l)) = (c.val.1 (Fin.last l)) • b
    rw [Algebra.smul_def,Algebra.commutes]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- The augmentation preserves the regular left B-action as well. -/
theorem augmentation_left (b : B) (x : term k B l l) :
    augmentation k B l (b • x) = b • augmentation k B l x := by
  change terminalAugmentation k B l (TensorIdeal.coefficient b * x.val) =
    b * terminalAugmentation k B l x.val
  rw [map_mul]
  congr 1
  change b * algebraMap k B (ChainAlgebra.terminalCharacter k l 1) = b
  rw [map_one,map_one,mul_one]

theorem augmentation_comp (n : ℕ) :
    (augmentation k B (n+1)).comp (differential k B (n+1) n) = 0 := by
  ext x
  change terminalAugmentation k B (n+1) (((1:B) ⊗ₜ[k] extendedArrow k (n+1) n) * x.val) = 0
  rw [map_mul]
  have hz : terminalAugmentation k B (n+1) ((1:B) ⊗ₜ[k] extendedArrow k (n+1) n) = 0 := by
    rw [extendedArrow,dite_eq_left (by omega)]
    change 1 * algebraMap k B ((arrow k (n+1) ⟨n,by omega⟩).1 (Fin.last (n+1))) = 0
    rw [arrow_diagonal,map_zero,mul_zero]
  rw [hz,zero_mul]

theorem augmentation_exact (n : ℕ) :
    Function.Exact (differential k B (n+1) n) (augmentation k B (n+1)) := by
  have hc : Function.Exact ((resolutionDifferential k (n+1) n).hom.restrictScalars k)
      ((resolutionAugmentation k (n+1)).hom.restrictScalars k) := by
    intro x
    constructor
    · intro hx
      exact (ShortComplex.moduleCat_exact_iff _).mp (resolutionAugmentation_exact k n) x hx
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f => f.hom y) (resolutionAugmentation_comp k n)
  have ht := Module.Flat.lTensor_exact B hc
  intro x
  constructor
  · intro hx
    have hz : (((resolutionAugmentation k (n+1)).hom.restrictScalars k).lTensor B)
        ((termEquiv k B (n+1) (n+1)).symm x) = 0 := by
      apply (terminalEquiv k B).injective
      rw [← augmentation_tensor,LinearEquiv.apply_symm_apply,hx,map_zero]
    obtain ⟨y,hy⟩ := (ht _).mp hz
    refine ⟨termEquiv k B (n+1) n y, ?_⟩
    rw [← termEquiv_d,hy,LinearEquiv.apply_symm_apply]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (augmentation_comp k B n)

/-- Surjectivity is explicit: the terminal vertex lifts every coefficient b. -/
theorem augmentation_surjective : Function.Surjective (augmentation k B l) := by
  intro b
  let x : term k B l l := ⟨(show B from b) ⊗ₜ[k] vertex k l (Fin.last l), by
    change ((1:B) ⊗ₜ[k] extendedVertex k l l) * _ = _
    rw [extendedVertex,dite_eq_left le_rfl]
    have hi : (⟨l,by omega⟩ : Fin (l+1)) = Fin.last l := rfl
    rw [hi,Algebra.TensorProduct.tmul_mul_tmul,one_mul,vertex_idempotent]⟩
  refine ⟨x, ?_⟩
  change (show B from b) * algebraMap k B ((vertex k l (Fin.last l)).1 (Fin.last l)) = (show B from b)
  rw [vertex_diagonal,Pi.single_eq_same,map_one,mul_one]

theorem initial_injective (h : 0 < l) : Function.Injective (differential k B l 0) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    ((resolutionDifferential k l 0).hom.restrictScalars k) (resolutionInitial_injective k l h) (M := B)
  intro x y hxy
  apply (termEquiv k B l 0).symm.injective
  apply hi
  apply (termEquiv k B l 1).injective
  rw [termEquiv_d,termEquiv_d,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,hxy]

theorem augmentation_zero_injective : Function.Injective (augmentation k B 0) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    ((resolutionAugmentation k 0).hom.restrictScalars k) (resolutionAugmentation_zero_injective k) (M := B)
  intro x y hxy
  apply (termEquiv k B 0 0).symm.injective
  apply hi
  apply (terminalEquiv k B).injective
  rw [← augmentation_tensor,← augmentation_tensor,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,hxy]
end TensorResolution
end LittleFinitistic.OrdinarySimulation

end

end OAI
