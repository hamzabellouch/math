import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethClass
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicExt
import OAI.Algebra.AuslanderReiten.Ext.TensorExtCoefficients

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

private theorem extMk_of_eq {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (L : ProjectiveResolution M) {n : ℕ} (f g : L.complex.X n ⟶ N)
    (hf : L.complex.d (n+1) n ≫ f=0) (hg : L.complex.d (n+1) n ≫ g=0) (hfg : f=g) :
    L.extMk f (n+1) rfl hf = L.extMk g (n+1) rfl hg := by
  subst g
  rfl

def elementaryExt (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    Ext (moduleObject k A B X Y) (moduleObject k A B U V) n :=
  (projectiveResolution k A B P Q).extMk
    (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
      (Y := moduleObject k A B U V) (elementaryHom k A B P.complex Q.complex U V i j n h f g))
    (n+1) rfl (ModuleCat.hom_ext (elementary_closed k A B P.complex Q.complex U V i j n h f g hf hg))

omit [CharP k 2] [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
  [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))] in
theorem elementaryExt_kunneth (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg) =
      (Pi.single ⟨(i,j),h⟩
        (P.extMk (ModuleCat.ofHom (X := P.complex.X i) (Y := U) f) (i+1) rfl (ModuleCat.hom_ext hf) ⊗ₜ[k]
          Q.extMk (ModuleCat.ofHom (X := Q.complex.X j) (Y := V) g) (j+1) rfl (ModuleCat.hom_ext hg)) :
        extCoefficients k A B X U Y V n) :=
  extKunnethEquiv_elementary k A B P Q U V i j n h f g hf hg

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)

omit [HasDerivedCategory (ModuleCat.{u} A)] [∀ n, Module.Finite A (P.complex.X n)] in
include hp in
theorem firstFactor_closed (i : ℕ) (f : P.complex.X i →ₗ[A] U)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) :
    (f.comp (p i).hom).comp (P.complex.d (i+4) (i+3)).hom=0 :=
  congrArg ModuleCat.Hom.hom (ResolutionProducts.cubicPrecomp_closed P p hp
    (ModuleCat.ofHom (X := P.complex.X i) (Y := U) f) (ModuleCat.hom_ext hf))

omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)] in
theorem firstCubicExt_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    (firstCubicExt k A B P Q p hp).comp
      (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega : 3+n=n+3) =
      elementaryExt k A B P Q U V (i+3) j (n+3) (by omega) (f.comp (p i).hom) g
        (firstFactor_closed A P U p hp i f hf) hg := by
  unfold elementaryExt
  erw [firstCubicExt_action]
  have he : firstComparison k A B P Q p n ≫
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
        (Y := moduleObject k A B U V) (elementaryHom k A B P.complex Q.complex U V i j n h f g) =
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X (n+3))
        (Y := moduleObject k A B U V)
        (elementaryHom k A B P.complex Q.complex U V (i+3) j (n+3) (by omega) (f.comp (p i).hom) g) :=
    ModuleCat.hom_ext (elementary_firstCubic k A B P.complex Q.complex U V p i j n h f g)
  exact extMk_of_eq (projectiveResolution k A B P Q) _ _ _ _ he

variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

omit [HasDerivedCategory (ModuleCat.{u} B)] [∀ n, Module.Finite B (Q.complex.X n)] in
include hr in
theorem secondFactor_closed (j : ℕ) (g : Q.complex.X j →ₗ[B] V)
    (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    (g.comp (r j).hom).comp (Q.complex.d (j+4) (j+3)).hom=0 :=
  congrArg ModuleCat.Hom.hom (ResolutionProducts.cubicPrecomp_closed Q r hr
    (ModuleCat.ofHom (X := Q.complex.X j) (Y := V) g) (ModuleCat.hom_ext hg))

omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)] in
theorem secondCubicExt_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    (secondCubicExt k A B P Q r hr).comp
      (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega : 3+n=n+3) =
      elementaryExt k A B P Q U V i (j+3) (n+3) (by omega) f (g.comp (r j).hom)
        hf (secondFactor_closed B Q V r hr j g hg) := by
  unfold elementaryExt
  erw [secondCubicExt_action]
  have he : secondComparison k A B P Q r n ≫
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
        (Y := moduleObject k A B U V) (elementaryHom k A B P.complex Q.complex U V i j n h f g) =
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X (n+3))
        (Y := moduleObject k A B U V)
        (elementaryHom k A B P.complex Q.complex U V i (j+3) (n+3) (by omega) f (g.comp (r j).hom)) :=
    ModuleCat.hom_ext (elementary_secondCubic k A B P.complex Q.complex U V r i j n h f g)
  exact extMk_of_eq (projectiveResolution k A B P Q) _ _ _ _ he

end ArExplicit.ExternalTensor

end

end OAI
