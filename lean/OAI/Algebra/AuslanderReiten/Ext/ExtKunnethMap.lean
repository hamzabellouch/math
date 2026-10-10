import OAI.Algebra.AuslanderReiten.Ext.ExtKunneth
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainNaturality
import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunnethMap

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k : Type u) [Field k]

private theorem tensor_conjugate {E F G H : Type u}
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
    [Module k E] [Module k F] [Module k G] [Module k H]
    (e : E ≃ₗ[k] F) (d : G ≃ₗ[k] H) (f : E →ₗ[k] E) (g : G →ₗ[k] G)
    (x : E ⊗[k] G) :
    TensorProduct.map e.toLinearMap d.toLinearMap (TensorProduct.map f g x) =
      TensorProduct.map (e.toLinearMap.comp (f.comp e.symm.toLinearMap))
        (d.toLinearMap.comp (g.comp d.symm.toLinearMap))
        (TensorProduct.map e.toLinearMap d.toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

private theorem homology_conjugate {K L : CochainComplex (ModuleCat.{u} k) ℕ}
    (e : K ≅ L) (f : K ⟶ K) (n : ℕ) (x : L.homology n) :
    ((homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso e).inv.hom
      ((homologyMap (e.inv ≫ f ≫ e.hom) n).hom x) =
    (homologyMap f n).hom
      (((homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso e).inv.hom x) := by
  have h : homologyMap (e.inv ≫ f ≫ e.hom) n ≫ homologyMap e.inv n =
      homologyMap e.inv n ≫ homologyMap f n := by
    rw [← homologyMap_comp, Category.assoc, Category.assoc, e.hom_inv_id,
      Category.comp_id, homologyMap_comp]
  exact congrArg (fun a => a.hom x) h

variable (R : Type u) [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (U : Type u) [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]

def nativeHomEndExt (f : homCochain k R P.complex U ⟶ homCochain k R P.complex U)
    (n : ℕ) : Ext X (ModuleCat.of R U) n →ₗ[k] Ext X (ModuleCat.of R U) n :=
  (homCochainNativeExtEquiv k R P U n).toLinearMap.comp
    ((homologyMap f n).hom.comp (homCochainNativeExtEquiv k R P U n).symm.toLinearMap)

variable (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [Module.Finite k A] [Module.Finite k B]
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (f : homCochain k A P.complex U ⟶ homCochain k A P.complex U)
variable (g : homCochain k B Q.complex V ⟶ homCochain k B Q.complex V)
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

def homTensorMap :
    homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex) (moduleObject k A B U V) ⟶
      homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex) (moduleObject k A B U V) :=
  (homCochainTotalIso k A B P.complex Q.complex U V).inv ≫
    mapBifunctorMap f g T (.up ℕ) ≫
      (homCochainTotalIso k A B P.complex Q.complex U V).hom

def homKunnethCoordinates (n : ℕ) :
    (homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).homology n ≃ₗ[k]
    (∀ p : Diagonal n, (homCochain k A P.complex U).homology p.val.1 ⊗[k]
      (homCochain k B Q.complex V).homology p.val.2) :=
  (homKunnethEquiv k A B P.complex Q.complex U V n).trans
    DFinsupp.linearEquivFunOnFintype

omit [Module.Finite k A] [Module.Finite k B] in

theorem homKunnethCoordinates_natural (n : ℕ)
    (x : (homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).homology n) :
    homKunnethCoordinates k A B P Q U V n
      ((homologyMap (homTensorMap k A B P Q U V f g) n).hom x) =
    VectorCochain.diagonalTermMap k (VectorCochain.gradedMap k f)
      (VectorCochain.gradedMap k g) n (homKunnethCoordinates k A B P Q U V n x) := by
  let e := homCochainTotalIso k A B P.complex Q.complex U V
  change VectorCochain.homologyCoordinates k n
      (((homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso e).inv.hom
        ((homologyMap (e.inv ≫ mapBifunctorMap f g T (.up ℕ) ≫ e.hom) n).hom x)) = _
  rw [homology_conjugate]
  exact VectorCochain.homologyCoordinates_natural k f g n _

def tensorHomEndExt (n : ℕ) :
    Ext (moduleObject k A B M N) (moduleObject k A B U V) n →ₗ[k]
      Ext (moduleObject k A B M N) (moduleObject k A B U V) n :=
  nativeHomEndExt k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) (homTensorMap k A B P Q U V f g) n

omit [Module.Finite k A] [Module.Finite k B] in
theorem extKunnethEquiv_apply (n : ℕ)
    (x : Ext (moduleObject k A B M N) (moduleObject k A B U V) n) (p : Diagonal n) :
    extKunnethEquiv k A B P Q U V n x p =
      TensorProduct.map (homCochainExtEquiv k A (Y := U) P p.val.1).toLinearMap
        (homCochainExtEquiv k B (Y := V) Q p.val.2).toLinearMap
        (homKunnethCoordinates k A B P Q U V n
          ((homCochainNativeExtEquiv k (A ⊗[k] B) (projectiveResolution k A B P Q)
            (moduleObject k A B U V) n).symm x) p) := rfl

omit [Module.Finite k A] [Module.Finite k B] in
theorem extKunnethEquiv_tensorHomEndExt (n : ℕ)
    (x : Ext (moduleObject k A B M N) (moduleObject k A B U V) n) (p : Diagonal n) :
    extKunnethEquiv k A B P Q U V n (tensorHomEndExt k A B P Q U V f g n x) p =
      TensorProduct.map (homCochainEndExt k A P f p.val.1)
        (homCochainEndExt k B Q g p.val.2)
        (extKunnethEquiv k A B P Q U V n x p) := by
  rw [extKunnethEquiv_apply, extKunnethEquiv_apply]
  let e := homCochainNativeExtEquiv k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) n
  change TensorProduct.map (homCochainExtEquiv k A (Y := U) P p.val.1).toLinearMap
      (homCochainExtEquiv k B (Y := V) Q p.val.2).toLinearMap
      (homKunnethCoordinates k A B P Q U V n
        (e.symm (e ((homologyMap (homTensorMap k A B P Q U V f g) n).hom (e.symm x)))) p) = _
  erw [LinearEquiv.symm_apply_apply, homKunnethCoordinates_natural]
  exact tensor_conjugate k (homCochainExtEquiv k A (Y := U) P p.val.1)
    (homCochainExtEquiv k B (Y := V) Q p.val.2) (homologyMap f p.val.1).hom
    (homologyMap g p.val.2).hom _

end ArExplicit.ExternalTensor

end

end OAI
