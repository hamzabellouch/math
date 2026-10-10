import OAI.NumberTheory.PiExponent.Cohomology.CechHigher
import OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechSections

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechHigher FreeCechResolution
open scoped Simplicial BigOperators

universe u
variable {X : TopCat.{u}} {J : Type u} (U : J → Opens X)

def canonicalTuple {q : ℕ} (t : Fin (q + 1) → J) :
    ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).obj (op (intersection U t)) :=
  fun i => ⟨t i, iInf_le (fun j => U (t j)) i⟩

def tupleNatEquiv (F : (Opens X)ᵒᵖ ⥤ Type u) (q : ℕ) :
    (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)) ⟶ F) ≃
      (∀ t : Fin (q + 1) → J, F.obj (op (intersection U t))) where
  toFun a t := a.app _ (canonicalTuple U t)
  invFun s :=
    { app W := ↾fun v =>
        F.map (homOfLE (le_iInf fun i => (v i).property)).op (s (fun i => (v i).val))
      naturality W V f := by
        ext v
        let t : Fin (q + 1) → J := fun i => (v i).val
        let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
        exact F.map_comp_apply (homOfLE h).op f (s t) }
  left_inv a := by
    ext W v
    let t : Fin (q + 1) → J := fun i => (v i).val
    let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
    have he : (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).map
        (homOfLE h).op) (canonicalTuple U t) = v := by
      funext i
      apply Subtype.ext
      rfl
    have hn := NatTrans.naturality_apply a (homOfLE h).op (canonicalTuple U t)
    rw [he] at hn
    exact hn.symm
  right_inv s := by
    funext t
    change F.map (𝟙 (op (intersection U t))) (s t) = s t
    rw [CategoryTheory.Functor.map_id]
    rfl

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

def freeTerm (q : ℕ) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)))

def sectionValuesEquiv (q : ℕ) : (freeTerm U R q ⟶ M) ≃
    (∀ t : Fin (q + 1) → J, M.val.obj (op (intersection U t))) :=
  ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeHomEquiv).trans (tupleNatEquiv U _ q)

def sectionsEquiv (q : ℕ) : (freeTerm U R q ⟶ M) ≃ Cochain R U M q :=
  (sectionValuesEquiv U R M q).trans
    (Equiv.piCongrRight fun t => (freeOpenEquiv R M (intersection U t)).symm)

def tupleEmbedding {q : ℕ} (t : Fin (q + 1) → J) :
    yoneda.obj (intersection U t) ⟶ (tuplePresheaf (coverVertices U)).obj (op ⦋q⦌) :=
  yonedaEquiv.symm (canonicalTuple U t)

def generator {q : ℕ} (t : Fin (q + 1) → J) :
    freeOpen R (intersection U t) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (tupleEmbedding U t))

theorem sectionsEquiv_apply (q : ℕ) (f : freeTerm U R q ⟶ M) (t : Fin (q + 1) → J) :
    sectionsEquiv U R M q f t = generator U R t ≫ f := by
  apply (freeOpenEquiv R M (intersection U t)).injective
  simp only [sectionsEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.apply_symm_apply]
  let g := (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f
  change (PresheafOfModules.freeHomEquiv g).app _ (canonicalTuple U t) =
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) (generator U R t ≫ f))
  symm
  have hs := congrArg PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left
      ((PresheafOfModules.free R.obj).map (tupleEmbedding U t)) f)
  have hf := congrArg yonedaEquiv
    ((PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
      (tupleEmbedding U t) g)
  exact hs.trans (hf.trans (yonedaEquiv_comp (tupleEmbedding U t)
    (PresheafOfModules.freeHomEquiv g)))

theorem tupleEmbedding_face {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    tupleEmbedding U t ≫ (tuplePresheaf (coverVertices U)).δ k =
      yoneda.map (homOfLE (faceLE U t k)) ≫ tupleEmbedding U (t ∘ k.succAbove) := by
  simp only [tupleEmbedding]
  ext W v
  funext i
  apply Subtype.ext
  rfl

def freeFace (q : ℕ) (k : Fin (q + 2)) : freeTerm U R (q + 1) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map ((tuplePresheaf (coverVertices U)).δ k))

theorem generator_face {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    generator U R t ≫ freeFace U R q k =
      freeOpenMap R (homOfLE (faceLE U t k)) ≫ generator U R (t ∘ k.succAbove) := by
  simp only [generator, freeFace]
  let F : ((Opens X)ᵒᵖ ⥤ Type u) ⥤ SheafOfModules.{u} R :=
    PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
  change F.map (tupleEmbedding U t) ≫ F.map ((tuplePresheaf (coverVertices U)).δ k) =
    F.map (yoneda.map (homOfLE (faceLE U t k))) ≫ F.map (tupleEmbedding U (t ∘ k.succAbove))
  exact (F.map_comp _ _).symm.trans
    ((congrArg (fun f => F.map f) (tupleEmbedding_face U t k)).trans (F.map_comp _ _))

def boundary (q : ℕ) : freeTerm U R (q + 1) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((freePresheafComplex R.obj (coverVertices U)).d (q + 1) q)

theorem boundary_eq_sum (q : ℕ) :
    boundary U R q = ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • freeFace U R q k := by
  let : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  dsimp only [boundary, freePresheafComplex, freeTerm]
  rw [AlternatingFaceMapComplex.obj_d_eq]
  rw [CategoryTheory.Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [CategoryTheory.Functor.map_zsmul]
  rfl

theorem boundary_squared (q : ℕ) : boundary U R (q + 1) ≫ boundary U R q = 0 := by
  unfold boundary
  erw [← CategoryTheory.Functor.map_comp, HomologicalComplex.d_comp_d,
    CategoryTheory.Functor.map_zero]
  rfl

def termShortComplex (q : ℕ) : ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk (boundary U R (q + 1)) (boundary U R q) (boundary_squared U R q)

theorem sectionsEquiv_boundary (q : ℕ) (f : freeTerm U R q ⟶ M) :
    sectionsEquiv U R M (q + 1) (boundary U R q ≫ f) =
      differential R U M (sectionsEquiv U R M q f) := by
  funext t
  rw [sectionsEquiv_apply, ← Category.assoc, boundary_eq_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, generator_face,
    Category.assoc, CechHigher.differential, sectionsEquiv_apply, CechOne.restrictHom]

theorem hasPrimitives_of_exact [Injective M] (q : ℕ)
    (hexact : (termShortComplex U R q).Exact) : HasPrimitives R U M q := by
  intro c hc
  let f := (sectionsEquiv U R M (q + 1)).symm c
  have hf : boundary U R (q + 1) ≫ f = 0 := by
    apply (sectionsEquiv U R M (q + 2)).injective
    rw [sectionsEquiv_boundary]
    have he : sectionsEquiv U R M (q + 1) f = c :=
      (sectionsEquiv U R M (q + 1)).apply_symm_apply c
    rw [he, hc]
    funext t
    rw [sectionsEquiv_apply, comp_zero]
    rfl
  let g : freeTerm U R q ⟶ M := hexact.descToInjective f hf
  refine ⟨sectionsEquiv U R M q g, ?_⟩
  rw [← sectionsEquiv_boundary]
  exact (congrArg (fun f : freeTerm U R (q + 1) ⟶ M => sectionsEquiv U R M (q + 1) f)
    (hexact.comp_descToInjective f hf)).trans
      ((sectionsEquiv U R M (q + 1)).apply_symm_apply c)

theorem injective_hasPrimitives [Injective M] (q : ℕ) : HasPrimitives R U M q := by
  apply hasPrimitives_of_exact U R M q
  have h := freeSheafComplex_exact R (coverVertices U) q
  exact (HomologicalComplex.exactAt_iff'
    (K := freeSheafComplex R (coverVertices U)) (i := q + 2) (j := q + 1) (k := q)
    (by simp) (by simp)).mp h

theorem ext_succ_eq_zero (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (n : ℕ)
    (hlocal : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
      (x : CategoryTheory.Abelian.Ext.{u+1}
        (freeOpen R (intersection U t)) M (k + 1)), x = 0)
    (hprimitive : HasPrimitives R U M n)
    (x : CategoryTheory.Abelian.Ext.{u+1} (freeOpen R V) M (n + 1)) : x = 0 := by
  exact ext_succ_eq_zero_of_injective_cech R U M V hUV hcover
    (fun I _ q => injective_hasPrimitives U R I q) n hlocal hprimitive x

private abbrev schemeFreeOpen (Y : AlgebraicGeometry.Scheme.{u}) (V : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero
    (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J),
      AlgebraicGeometry.IsAffineOpen (intersection W t))
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : CategoryTheory.Abelian.Ext.{u+1} (C := Y.Modules)
      (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact affine_ext_succ_eq_zero_of_injective_cech Y A W V hWV hcover haffine
    (fun I hI q => @injective_hasPrimitives _ _ W Y.ringCatSheaf I hI q) n hprimitive x

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
