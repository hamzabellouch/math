import OAI.Algebra.Finitistic.Ordinary.OrdinaryCompression
import Mathlib.Algebra.Algebra.Opposite

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
universe u
/-- A genuine tensor-algebra module with both scalar restrictions recorded together. -/
def BimoduleCoefficients (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
    (M : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) := M
namespace BimoduleCoefficients
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (M : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ))
instance : AddCommGroup (BimoduleCoefficients k S A M) := inferInstanceAs (AddCommGroup M)
instance : Module (S ⊗[k] Aᵐᵒᵖ) (BimoduleCoefficients k S A M) := inferInstanceAs (Module (S ⊗[k] Aᵐᵒᵖ) M)
instance : Module k (BimoduleCoefficients k S A M) := Module.compHom _ (algebraMap k (S ⊗[k] Aᵐᵒᵖ))
instance : Module S (BimoduleCoefficients k S A M) := Module.compHom _
  (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom
instance : Module Aᵐᵒᵖ (BimoduleCoefficients k S A M) := Module.compHom _
  (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom
instance towerLeft : IsScalarTower k S (BimoduleCoefficients k S A M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := S) (B := Aᵐᵒᵖ) (algebraMap k S r)) • (m : M) =
    (algebraMap k (S ⊗[k] Aᵐᵒᵖ) r) • (m : M)
  rw [AlgHom.commutes]
instance towerRight : IsScalarTower k Aᵐᵒᵖ (BimoduleCoefficients k S A M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ) (algebraMap k Aᵐᵒᵖ r)) • (m : M) =
    (algebraMap k (S ⊗[k] Aᵐᵒᵖ) r) • (m : M)
  rw [AlgHom.commutes]
instance commute : SMulCommClass S Aᵐᵒᵖ (BimoduleCoefficients k S A M) where
  smul_comm s a m := by
    change (s ⊗ₜ[k] (1:Aᵐᵒᵖ)) • (((1:S) ⊗ₜ[k] a) • (m : M)) =
      ((1:S) ⊗ₜ[k] a) • ((s ⊗ₜ[k] (1:Aᵐᵒᵖ)) • (m : M))
    rw [← mul_smul,← mul_smul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

variable {M} {M' : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)}
def map (f : M ⟶ M') : BimoduleCoefficients k S A M →ₗ[Aᵐᵒᵖ] BimoduleCoefficients k S A M' where
  __ := f.hom.toAddHom
  map_smul' a m := f.hom.map_smul (((1:S) ⊗ₜ[k] a)) m

theorem map_left (f : M ⟶ M') (s : S) (m : BimoduleCoefficients k S A M) :
    map k S A f (s • m) = s • map k S A f m :=
  f.hom.map_smul (s ⊗ₜ[k] (1:Aᵐᵒᵖ)) m
end BimoduleCoefficients
end LittleFinitistic

end

end OAI
