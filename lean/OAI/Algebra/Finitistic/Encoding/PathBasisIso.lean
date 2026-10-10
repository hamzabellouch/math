import OAI.Algebra.Finitistic.Encoding.ArrowBasisIso
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.PathBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)
abbrev family : Fin (d+1) → ModuleCat.{u} k := fun _ => ModuleCat.of k (QuadraticEncoding.Arrows k d)

/-- Group paths by their first traversed arrow; the later arrow is the first tensor factor. -/
def iso : (⨁ family k d) ≅ ModuleCat.of k (QuadraticEncoding.Paths k d) :=
  ModuleCat.biproductIsoPi (family k d) ≪≫
    (TensorProduct.piScalarRight k k (QuadraticEncoding.Arrows k d) (Fin (d+1))).symm.toModuleIso

theorem pi_hom_proj (j : Fin (d+1)) :
    (ModuleCat.biproductIsoPi (family k d)).hom ≫ ModuleCat.ofHom (LinearMap.proj j) =
      biproduct.π (family k d) j := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (family k d) j]
  simp only [Iso.hom_inv_id_assoc]

theorem pi_injection_apply (a : Fin (d+1)) (w : QuadraticEncoding.Arrows k d) :
    (biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w = Pi.single a w := by
  funext j
  have h := congrArg (fun f : (family k d a) ⟶ family k d j => f.hom w)
    (congrArg (fun f => biproduct.ι (family k d) a ≫ f) (pi_hom_proj k d j))
  change ((biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w) j = _
  rw [show ((biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w) j =
      (biproduct.ι (family k d) a ≫ biproduct.π (family k d) j).hom w from h]
  classical
  by_cases haj : a=j
  · subst j; simp
  · simp [haj,Ne.symm haj]

/-- A summand w at a maps to the actual tensor path w tensor a. -/
theorem injection_apply (a : Fin (d+1)) (w : QuadraticEncoding.Arrows k d) :
    (biproduct.ι (family k d) a ≫ (iso k d).hom).hom w = w ⊗ₜ[k] QuadraticEncoding.basis a := by
  change (TensorProduct.piScalarRight k k (QuadraticEncoding.Arrows k d) (Fin (d+1))).symm
    ((biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w) = _
  rw [pi_injection_apply,TensorProduct.piScalarRight_symm_single]
  rfl
end LittleFinitistic.PathBasisIso

end

end OAI
