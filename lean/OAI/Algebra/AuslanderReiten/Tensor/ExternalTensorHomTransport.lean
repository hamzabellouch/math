import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethMap

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (f : homCochain k A P.complex U ⟶ homCochain k A P.complex U)
variable (g : homCochain k B Q.complex V ⟶ homCochain k B Q.complex V)
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

theorem homCochainTermCoordinates_natural (n : ℕ)
    (x : (homCochainTotal k A B P.complex Q.complex U V).X n) (p : Diagonal n) :
    homCochainTermCoordinates k A B P.complex Q.complex U V n
        (((mapBifunctorMap f g T (.up ℕ)).f n).hom x) p =
      TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom
        (homCochainTermCoordinates k A B P.complex Q.complex U V n x p) := by
  exact congrFun (VectorCochain.totalTermCoordinates_natural k f g n x) p

variable [∀ degree, Module.Finite A (P.complex.X degree)]
  [∀ degree, Module.Finite B (Q.complex.X degree)]

theorem homTensorMap_restrict (n : ℕ)
    (x : (homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).X n) (p : Diagonal n) :
    (((homTensorMap k A B P Q U V f g).f n).hom x).comp
        (inclusion k A B P.complex Q.complex p.val.1 p.val.2 n p.property).hom =
      homMap k A B (TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom
        (homCochainTermCoordinates k A B P.complex Q.complex U V n
          ((homCochainTermEquiv k A B P.complex Q.complex U V n).symm x) p)) := by
  change (homCochainTermEquiv k A B P.complex Q.complex U V n
      (((mapBifunctorMap f g T (.up ℕ)).f n).hom
        ((homCochainTermEquiv k A B P.complex Q.complex U V n).symm x))).comp _ = _
  rw [homCochainTermEquiv_restrict, homCochainTermCoordinates_natural]

end ArExplicit.ExternalTensor

end

end OAI
