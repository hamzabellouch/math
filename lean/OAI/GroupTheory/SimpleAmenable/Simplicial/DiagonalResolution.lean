import Mathlib

namespace OAI

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
namespace DiagonalResolution

abbrev D := SimplexCategory × SimplexCategory
abbrev A := ModuleCat.{0} ℤ
noncomputable abbrev Z : A := ModuleCat.of ℤ ℤ
noncomputable abbrev free (d : D) : D ⥤ A := (evaluationLeftAdjoint A d).obj Z

noncomputable def pre {a b : D} (k : a ⟶ b) : free b ⟶ free a where
  app d := Sigma.desc (fun f => Sigma.ι (fun _ : a ⟶ d => Z) (k ≫ f))
  naturality d e f := by
    apply Sigma.hom_ext
    intro g
    simp [free,evaluationLeftAdjoint,Category.assoc]

@[reassoc (attr := simp)] lemma ι_pre {a b : D} (k : a ⟶ b) (d : D) (f : b ⟶ d) :
    Sigma.ι (fun _ : b ⟶ d => Z) f ≫ (pre k).app d =
      Sigma.ι (fun _ : a ⟶ d => Z) (k ≫ f) := by
  exact Sigma.ι_comp_desc _ _

@[simp] lemma pre_id (a : D) : pre (𝟙 a) = 𝟙 (free a) := by
  apply NatTrans.ext
  funext d
  apply Sigma.hom_ext
  intro f
  simp only [ι_pre, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm
@[simp] lemma pre_comp {a b c : D} (f : a ⟶ b) (g : b ⟶ c) :
    pre (f ≫ g) = pre g ≫ pre f := by
  apply NatTrans.ext
  funext d
  apply Sigma.hom_ext
  intro h
  simp only [NatTrans.comp_app]
  erw [← Category.assoc, ι_pre, ι_pre, ι_pre]
  rw [Category.assoc]

noncomputable def preDiag {a b : SimplexCategory} (f : a ⟶ b) : free (b,b) ⟶ free (a,a) :=
  pre (a := (a,a)) (b := (b,b)) (f,f)

noncomputable def chains : SimplicialObject (D ⥤ A) where
  obj n := free (n.unop,n.unop)
  map f := pre (f.unop,f.unop)
  map_id n := pre_id _
  map_comp {X Y W} f g := by
    simpa only [unop_comp, prod_comp, Prod.mkHom] using (pre_comp (a := (W.unop,W.unop))
      (b := (Y.unop,Y.unop)) (c := (X.unop,X.unop)) (g.unop,g.unop) (f.unop,f.unop))
noncomputable def augmentation : chains ⟶ (SimplicialObject.const _).obj ((Functor.const D).obj Z) where
  app n :=
    { app d := Sigma.desc (fun _ : (n.unop,n.unop) ⟶ d => 𝟙 Z)
      naturality d e f := by
        apply Sigma.hom_ext
        intro g
        simp [chains,free,evaluationLeftAdjoint] }
  naturality n m f := by
    apply NatTrans.ext
    funext d
    apply Sigma.hom_ext
    intro g
    simp only [NatTrans.comp_app, chains, pre, Functor.const_obj_map]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      NatTrans.id_app, Category.id_comp]
    rfl

noncomputable def augmented : SimplicialObject.Augmented (D ⥤ A) where
  left := chains
  right := (Functor.const D).obj Z
  hom := augmentation

noncomputable def complex : ChainComplex (D ⥤ A) ℕ :=
  AlternatingFaceMapComplex.obj chains

instance projective (n : ℕ) : Projective (complex.X n) := by
  change Projective (free (⦋n⦌,⦋n⦌))
  exact (evaluationAdjunctionRight A (⦋n⦌,⦋n⦌)).map_projective Z inferInstance

open SSet.Augmented.StandardSimplex

def zeroSimplex (a : SimplexCategory) : ⦋0⦌ ⟶ a := SimplexCategory.Hom.mk (OrderHom.const _ 0)

@[simp] lemma shift_δ₀ {n : ℕ} {a : SimplexCategory} (f : ⦋n⦌ ⟶ a) :
    SimplexCategory.δ 0 ≫ shift f = f := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s_comp_δ₀ n)
      (SSet.stdSimplex.objEquiv.symm f))

@[simp] lemma shift_δ_succ {n : ℕ} {a : SimplexCategory} (f : ⦋n+1⦌ ⟶ a) (i : Fin (n+2)) :
    SimplexCategory.δ i.succ ≫ shift f = shift (SimplexCategory.δ i ≫ f) := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s_comp_δ n i)
      (SSet.stdSimplex.objEquiv.symm f))

@[simp] lemma shift_σ_succ {n : ℕ} {a : SimplexCategory} (f : ⦋n⦌ ⟶ a) (i : Fin (n+1)) :
    SimplexCategory.σ i.succ ≫ shift f = shift (SimplexCategory.σ i ≫ f) := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s_comp_σ n i)
      (SSet.stdSimplex.objEquiv.symm f))

@[simp] lemma shift_δ₁ {a : SimplexCategory} (f : ⦋0⦌ ⟶ a) :
    SimplexCategory.δ 1 ≫ shift f = zeroSimplex a := by
  exact congrArg SSet.stdSimplex.objEquiv.{0}
    (ConcreteCategory.congr_hom ((SSet.Augmented.StandardSimplex.extraDegeneracy a).s₀_comp_δ₁)
      (SSet.stdSimplex.objEquiv.symm f))

noncomputable abbrev augmentedAt (d : D) : SimplicialObject.Augmented A :=
  ((SimplicialObject.Augmented.whiskering _ _).obj ((evaluation D A).obj d)).obj augmented
noncomputable def extraAt (d : D) : (augmentedAt d).ExtraDegeneracy where
  s' := Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) (zeroSimplex d.1,zeroSimplex d.2)
  s n := Sigma.desc (fun f : (⦋n⦌,⦋n⦌) ⟶ d =>
    Sigma.ι (fun _ : (⦋n+1⦌,⦋n+1⦌) ⟶ d => Z) (shift f.1,shift f.2))
  s'_comp_ε := by
    change Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) (zeroSimplex d.1,zeroSimplex d.2) ≫
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z) = 𝟙 Z
    simp
  s₀_comp_δ₁ := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.δ 1)).app d =
      Sigma.desc _ ≫ Sigma.ι _ _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_comp_desc_assoc, ι_pre, Sigma.ι_comp_desc_assoc]
    simp only [prod_comp, Prod.mkHom, shift_δ₁]
    exact (Category.id_comp _).symm
  s_comp_δ₀ n := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.δ 0)).app d = 𝟙 _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_comp_desc_assoc, ι_pre]
    simp only [prod_comp, Prod.mkHom, shift_δ₀, Prod.eta]
    exact (Category.comp_id _).symm
  s_comp_δ n i := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.δ i.succ)).app d =
      (preDiag (SimplexCategory.δ i)).app d ≫ Sigma.desc _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_comp_desc_assoc, ι_pre, ι_pre_assoc, Sigma.ι_comp_desc]
    simp only [prod_comp, Prod.mkHom, shift_δ_succ]
    rfl
  s_comp_σ n i := by
    change Sigma.desc _ ≫ (preDiag (SimplexCategory.σ i.succ)).app d =
      (preDiag (SimplexCategory.σ i)).app d ≫ Sigma.desc _
    apply Sigma.hom_ext
    intro f
    dsimp only [preDiag]
    erw [Sigma.ι_comp_desc_assoc, ι_pre, ι_pre_assoc, Sigma.ι_comp_desc]
    simp only [prod_comp, Prod.mkHom, shift_σ_succ]
    rfl

noncomputable def pi : complex ⟶ (ChainComplex.single₀ (D ⥤ A)).obj ((Functor.const D).obj Z) :=
  AlternatingFaceMapComplex.ε.app augmented

noncomputable def atIso (d : D) :
    (((evaluation D A).obj d).mapHomologicalComplex (ComplexShape.down ℕ)).obj complex ≅
      AlternatingFaceMapComplex.obj (augmentedAt d).left :=
  eqToIso (congrArg (fun F => F.obj chains)
    (map_alternatingFaceMapComplex ((evaluation D A).obj d)))

noncomputable def singleAtIso (d : D) :
    (((evaluation D A).obj d).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ (D ⥤ A)).obj ((Functor.const D).obj Z)) ≅
      (ChainComplex.single₀ A).obj Z :=
  (HomologicalComplex.singleMapHomologicalComplex ((evaluation D A).obj d)
    (ComplexShape.down ℕ) 0).app ((Functor.const D).obj Z)
instance pi_quasiIso : QuasiIso pi := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro d
  let f := (((evaluation D A).obj d).mapHomologicalComplex (ComplexShape.down ℕ)).map pi
  have h : f ≫ (singleAtIso d).hom = (atIso d).hom ≫ (extraAt d).homotopyEquiv.hom := by
    apply HomologicalComplex.to_single_hom_ext
    dsimp [f,pi,atIso,singleAtIso]
    simp [HomologicalComplex.singleMapHomologicalComplex,
      SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
      Functor.mapHomologicalComplex, augmentedAt, augmented, augmentation]
    dsimp only [NatIso.ofComponents, SimplicialObject.Augmented.whiskering,
      SimplicialObject.Augmented.whiskeringObj, CategoryTheory.eqToIso]
    erw [HomologicalComplex.eqToHom_f]
    rfl
  change QuasiIso f
  rw [← quasiIso_iff_comp_right f (singleAtIso d).hom, h]
  have : QuasiIso (extraAt d).homotopyEquiv.hom :=
    (extraAt d).homotopyEquiv.quasiIso_hom
  have hcomp := quasiIso_comp (atIso d).hom (extraAt d).homotopyEquiv.hom
  exact hcomp

noncomputable def resolution : ProjectiveResolution ((Functor.const D).obj Z) where
  complex := complex
  π := pi
  quasiIso := pi_quasiIso

end DiagonalResolution

end OAI
