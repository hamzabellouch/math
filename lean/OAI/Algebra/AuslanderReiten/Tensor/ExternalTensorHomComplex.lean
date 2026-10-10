import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHom
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorForget
import OAI.Algebra.AuslanderReiten.Homology.CochainNatTensorSigns

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

def homCochain (U : Type u) [AddCommGroup U] [Module A U] [Module k U]
    [IsScalarTower k A U] : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (P.X n →ₗ[A] U))
    (fun n => ModuleCat.ofHom (LinearMap.lcomp k U (P.d (n+1) n).hom)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro x
      change f ((P.d (n+1) n).hom ((P.d (n+2) (n+1)).hom x)) = 0
      have hz := congrArg (fun g => g.hom x) (P.d_comp_d (n+2) (n+1) n)
      change (P.d (n+1) n).hom ((P.d (n+2) (n+1)).hom x) = 0 at hz
      rw [hz, map_zero])

@[simp] theorem homCochain_d (U : Type u) [AddCommGroup U] [Module A U] [Module k U]
    [IsScalarTower k A U] (n : ℕ) :
    (homCochain k A P U).d n (n+1) =
      ModuleCat.ofHom (LinearMap.lcomp k U (P.d (n+1) n).hom) :=
  by
    exact CochainComplex.of_d (V := ModuleCat.{u} k)
      (fun n => ModuleCat.of k (P.X n →ₗ[A] U))
      (fun n => ModuleCat.ofHom (LinearMap.lcomp k U (P.d (n+1) n).hom)) n

variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

instance hasHomCochainTotal : HasMapBifunctor (homCochain k A P U) (homCochain k B Q V)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) := fun _ => inferInstance

abbrev homCochainTotal : CochainComplex (ModuleCat.{u} k) ℕ :=
  mapBifunctor (homCochain k A P U) (homCochain k B Q V)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)

def homOutTerm (n : ℕ) :
    ((complex k A B P Q).X n →ₗ[A ⊗[k] B] moduleObject k A B U V) →ₗ[k]
      (∀ p : Diagonal n, summands k A B P Q n p →ₗ[A ⊗[k] B] moduleObject k A B U V) where
  toFun f p := f.comp (inclusion k A B P Q p.val.1 p.val.2 n p.property).hom
  map_add' f g := by funext p; exact LinearMap.add_comp _ _ _
  map_smul' a f := by funext p; exact LinearMap.smul_comp _ _ _

theorem homOutTerm_bijective (n : ℕ) : Function.Bijective (homOutTerm k A B P Q U V n) := by
  constructor
  · intro f g hfg
    have hh : ModuleCat.ofHom f = ModuleCat.ofHom g := by
      apply hom_ext k A B P Q
      intro i j hij
      exact ModuleCat.hom_ext (congrFun hfg ⟨(i,j),hij⟩)
    exact congrArg (fun h => h.hom) hh
  · intro f
    refine ⟨(desc k A B P Q (fun i j hij => ModuleCat.ofHom (X := moduleObject k A B (P.X i) (Q.X j))
        (Y := moduleObject k A B U V) (f ⟨(i,j),hij⟩))).hom, ?_⟩
    funext p
    exact congrArg (fun h => h.hom)
      (inclusion_desc k A B P Q (fun i j hij => ModuleCat.ofHom (X := moduleObject k A B (P.X i) (Q.X j))
        (Y := moduleObject k A B U V) (f ⟨(i,j),hij⟩))
        p.val.1 p.val.2 p.property)

def homOutTermEquiv (n : ℕ) :
    ((complex k A B P Q).X n →ₗ[A ⊗[k] B] moduleObject k A B U V) ≃ₗ[k]
      (∀ p : Diagonal n, summands k A B P Q n p →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  LinearEquiv.ofBijective (homOutTerm k A B P Q U V n) (homOutTerm_bijective k A B P Q U V n)

abbrev homCochainSummand (n : ℕ) (p : Diagonal n) : ModuleCat.{u} k :=
  ModuleCat.of k ((P.X p.val.1 →ₗ[A] U) ⊗[k] (Q.X p.val.2 →ₗ[B] V))

def homCochainTermCoordinates (n : ℕ) :
    (homCochainTotal k A B P Q U V).X n ≃ₗ[k]
      (∀ p : Diagonal n, homCochainSummand k A B P Q U V n p) :=
  (ModuleCat.coprodIsoDirectSum (homCochainSummand k A B P Q U V n)).toLinearEquiv.trans
    DFinsupp.linearEquivFunOnFintype

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

def homCochainTermEquiv (n : ℕ) :
    (homCochainTotal k A B P Q U V).X n ≃ₗ[k]
      (homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V)).X n :=
  (homCochainTermCoordinates k A B P Q U V n).trans
    ((LinearEquiv.piCongrRight fun p => homEquiv k A B
      (M := P.X p.val.1) (N := Q.X p.val.2) (U := U) (V := V)).trans
      (homOutTermEquiv k A B P Q U V n).symm)

abbrev homCochainInclusion (i j n : ℕ) (h : i+j=n) :
    homCochainSummand k A B P Q U V n ⟨(i,j),h⟩ ⟶ (homCochainTotal k A B P Q U V).X n :=
  ιMapBifunctor (homCochain k A P U) (homCochain k B Q V)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j n h

theorem homCochainTermEquiv_restrict (n : ℕ) (x : (homCochainTotal k A B P Q U V).X n)
    (p : Diagonal n) :
    (homCochainTermEquiv k A B P Q U V n x).comp
      (inclusion k A B P Q p.val.1 p.val.2 n p.property).hom =
      homMap k A B (homCochainTermCoordinates k A B P Q U V n x p) := by
  exact congrFun ((homOutTermEquiv k A B P Q U V n).apply_symm_apply
    ((LinearEquiv.piCongrRight fun p => homEquiv k A B
      (M := P.X p.val.1) (N := Q.X p.val.2) (U := U) (V := V))
        (homCochainTermCoordinates k A B P Q U V n x))) p

omit [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
  [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)] in
theorem homCochainTermCoordinates_inclusion (i j n : ℕ) (h : i+j=n)
    (x : (P.X i →ₗ[A] U) ⊗[k] (Q.X j →ₗ[B] V)) :
    homCochainTermCoordinates k A B P Q U V n (homCochainInclusion k A B P Q U V i j n h x) =
      Pi.single ⟨(i,j),h⟩ x := by
  have hh := congrArg (fun f => f.hom x)
    (ModuleCat.ι_coprodIsoDirectSum_hom (homCochainSummand k A B P Q U V n) ⟨(i,j),h⟩)
  exact congrArg (fun y => DFinsupp.linearEquivFunOnFintype (R := k) y) hh

@[simp] theorem homCochainTermEquiv_inclusion_same (i j n : ℕ) (h : i+j=n)
    (x : (P.X i →ₗ[A] U) ⊗[k] (Q.X j →ₗ[B] V)) :
    (homCochainTermEquiv k A B P Q U V n (homCochainInclusion k A B P Q U V i j n h x)).comp
      (inclusion k A B P Q i j n h).hom = homMap k A B x := by
  exact (homCochainTermEquiv_restrict k A B P Q U V n _ ⟨(i,j),h⟩).trans
    (congrArg (homMap k A B) ((congrFun (homCochainTermCoordinates_inclusion k A B P Q U V i j n h x) ⟨(i,j),h⟩).trans (Pi.single_eq_same _ _)))

@[simp] theorem homCochainTermEquiv_inclusion_ne (i j n : ℕ) (h : i+j=n)
    (x : (P.X i →ₗ[A] U) ⊗[k] (Q.X j →ₗ[B] V)) (a b : ℕ) (hab : a+b=n)
    (hne : (a,b) ≠ (i,j)) :
    (homCochainTermEquiv k A B P Q U V n (homCochainInclusion k A B P Q U V i j n h x)).comp
      (inclusion k A B P Q a b n hab).hom = 0 := by
  refine (homCochainTermEquiv_restrict k A B P Q U V n _ ⟨(a,b),hab⟩).trans ?_
  rw [homCochainTermCoordinates_inclusion,
    Pi.single_eq_of_ne (show (⟨(a,b),hab⟩ : Diagonal n) ≠ ⟨(i,j),h⟩ from fun hh => hne (congrArg Subtype.val hh)),
    map_zero]

end ArExplicit.ExternalTensor

end

end OAI
