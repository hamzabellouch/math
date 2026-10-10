import OAI.Algebra.Finitistic.Ordinary.OrdinaryResolutionComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Single

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- In the supported range, the extended ideal is the source's actual right projective. -/
def supportedIdealEquiv (n : ℕ) (h : n ≤ l) :
    resolutionIdeal k l n ≃ₗ[(ChainAlgebra k l)ᵐᵒᵖ] rightTerm (k := k) (⟨n,by omega⟩ : Fin (l+1)) where
  toFun x := ⟨x.val, by
    have hp := x.property
    change extendedVertex k l n * x.val = x.val at hp
    change vertex k l ⟨n,by omega⟩ * x.val = x.val
    simpa only [extendedVertex, dite_eq_left h] using hp⟩
  invFun x := ⟨x.val, by
    change extendedVertex k l n * x.val = x.val
    rw [extendedVertex, dite_eq_left h]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem supportedIdealEquiv_d (n : ℕ) (h : n < l) (x : resolutionIdeal k l n) :
    supportedIdealEquiv k l (n+1) (by omega) ((resolutionDifferential k l n).hom x) =
      resolutionMap (k := k) ⟨n,h⟩ (supportedIdealEquiv k l n (by omega) x) := by
  apply Subtype.ext
  change extendedArrow k l n * x.val = arrow k l ⟨n,h⟩ * x.val
  rw [extendedArrow, dite_eq_left h]

/-- The actual bundled complex is exact at every interior degree. -/
theorem supported_complex_exact (n : ℕ) (h : n+1 < l) :
    (ShortComplex.mk (resolutionDifferential k l n) (resolutionDifferential k l (n+1))
      (resolutionDifferential_square k l n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' := congrArg (supportedIdealEquiv k l (n+2) (by omega)) hx
  rw [supportedIdealEquiv_d k l (n+1) h, map_zero] at hx'
  obtain ⟨y,hy⟩ := (resolution_exact (k := k) n h (supportedIdealEquiv k l (n+1) (by omega) x)).mp hx'
  refine ⟨(supportedIdealEquiv k l n (by omega)).symm y, ?_⟩
  apply (supportedIdealEquiv k l (n+1) (by omega)).injective
  rw [supportedIdealEquiv_d k l n (by omega), LinearEquiv.apply_symm_apply, hy]

/-- The actual augmentation of the bundled complex in its last degree. -/
def resolutionAugmentation : resolutionTerm k l l ⟶ ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k) :=
  ModuleCat.ofHom ((augmentation k l).comp (supportedIdealEquiv k l l le_rfl).toLinearMap)

/-- A genuine chain map to the terminal simple placed in degree l. -/
def terminalAugmentationMap : terminalProjectiveComplex k l ⟶
    (HomologicalComplex.single _ (.up ℕ) l).obj (ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k)) :=
  HomologicalComplex.mkHomToSingle (resolutionAugmentation k l) (by
    intro i hi
    change i+1=l at hi
    subst l
    change CochainComplex.of.d _ _ i (i+1) ≫ resolutionAugmentation k (i+1) = 0
    rw [CochainComplex.of_d]
    ext x
    change (extendedArrow k (i+1) i * x.val).1 (Fin.last (i+1)) = (0:k)
    rw [extendedArrow, dite_eq_left (by omega), mul_diagonal, arrow_diagonal, zero_mul])
end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
