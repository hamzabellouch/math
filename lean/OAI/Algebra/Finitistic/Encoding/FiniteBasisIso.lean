import Mathlib.Algebra.Category.ModuleCat.Biproducts
import OAI.Algebra.Finitistic.Encoding.RelationBasisCoefficients

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteBasisIso
universe u
variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
variable {I : Type} [Fintype I] (b : Module.Basis I k V)
abbrev family : I → ModuleCat.{u} k := fun _ => ModuleCat.of k k

/-- An actual finite basis gives the scalar-column isomorphism, including the empty basis. -/
def iso : (⨁ (family (k := k) : I → _)) ≅ ModuleCat.of k V :=
  ModuleCat.biproductIsoPi _ ≪≫ b.equivFun.symm.toModuleIso

theorem pi_hom_proj (j : I) :
    (ModuleCat.biproductIsoPi (family (k := k) : I → _)).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (family (k := k) : I → _) j]
  simp only [Iso.hom_inv_id_assoc]

theorem injection_apply (i : I) (c : k) :
    (biproduct.ι (family (k := k) : I → _) i ≫ (iso b).hom).hom c = c • b i := by
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm ((ModuleCat.Hom.hom
    (biproduct.ι (family (k := k) : I → _) i ≫ (ModuleCat.biproductIsoPi _).hom)) c)) =
      b.equivFun (c • b i)
  rw [LinearEquiv.apply_symm_apply]
  funext j
  have h := congrArg (fun f : ModuleCat.of k k ⟶ ModuleCat.of k k => f.hom c)
    (congrArg (fun f => biproduct.ι (family (k := k) : I → _) i ≫ f)
      (pi_hom_proj (k := k) j))
  rw [show ((biproduct.ι (family (k := k) : I → _) i ≫
      (ModuleCat.biproductIsoPi _).hom).hom c) j =
      (biproduct.ι (family (k := k) : I → _) i ≫ biproduct.π _ j).hom c from h]
  classical
  by_cases hij : i=j
  · subst j; simp
  · simp [hij,Ne.symm hij]
end LittleFinitistic.FiniteBasisIso

end

end OAI
