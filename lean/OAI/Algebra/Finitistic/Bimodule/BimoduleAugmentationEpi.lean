import OAI.Algebra.Finitistic.Bimodule.BimoduleAugmentedResolution
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- A quasi-isomorphism onto a stalk is surjective in each degree; this is
proved from its homology map, not imposed on the resolution data. -/
theorem augmentation_epi_f (n : ℤ) : Epi (res.augmentation.f n) := by
  let T := bimoduleStalk k B X
  let := res.quasiIso
  have : IsIso (T.homologyπ n) := T.isIso_homologyπ (n-1) n (by simp) (by simp [T,bimoduleStalk])
  have : IsIso (T.iCycles n) := T.isIso_iCycles n (n+1) (by simp) (by simp [T,bimoduleStalk])
  have heq : cyclesMap res.augmentation n = P.homologyπ n ≫
      homologyMap res.augmentation n ≫ inv (T.homologyπ n) := by
    rw [← Category.assoc,homologyπ_naturality,Category.assoc,IsIso.hom_inv_id,Category.comp_id]
  have : Epi (cyclesMap res.augmentation n) := by
    rw [heq]
    infer_instance
  have : Epi (P.iCycles n ≫ res.augmentation.f n) := by
    rw [← cyclesMap_i]
    infer_instance
  exact epi_of_epi (P.iCycles n) (res.augmentation.f n)
end LittleFinitistic.BimoduleTotal

end

end OAI
