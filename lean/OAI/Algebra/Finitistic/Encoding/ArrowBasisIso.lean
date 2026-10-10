import Mathlib.Algebra.Category.ModuleCat.Biproducts
import OAI.Algebra.Finitistic.Rectification.TensorComplex
import OAI.Algebra.Finitistic.Encoding.RelationBasisCoefficients

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ArrowBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)

abbrev family : Fin (d+1) → ModuleCat.{u} k := fun _ => ModuleCat.of k k

/-- The adjacent arrow space is precisely the direct sum of its scalar arrow columns. -/
def iso : (⨁ family k d) ≅ ModuleCat.of k (QuadraticEncoding.Arrows k d) :=
  ModuleCat.biproductIsoPi (family k d)

theorem hom_proj (j : Fin (d+1)) :
    (iso k d).hom ≫ ModuleCat.ofHom (LinearMap.proj j) = biproduct.π (family k d) j := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (family k d) j]
  simp only [iso,Iso.hom_inv_id_assoc]

/-- The coproduct injection sends a scalar to that scalar times its original arrow basis. -/
theorem injection_apply (i : Fin (d+1)) (c : k) :
    ((biproduct.ι (family k d) i ≫ (iso k d).hom).hom) c =
      c • QuadraticEncoding.basis i := by
  funext j
  have h := congrArg (fun f : (family k d i) ⟶ ModuleCat.of k k => f.hom c)
    (congrArg (fun f => biproduct.ι (family k d) i ≫ f) (hom_proj k d j))
  have h' : ((biproduct.ι (family k d) i ≫ (iso k d).hom).hom c) j =
      (biproduct.ι (family k d) i ≫ biproduct.π (family k d) j).hom c := h
  rw [h']
  classical
  by_cases hij : i=j
  · subst j
    simp [QuadraticEncoding.basis]
  · simp [hij,QuadraticEncoding.basis,Ne.symm hij]
end LittleFinitistic.ArrowBasisIso

end

end OAI
