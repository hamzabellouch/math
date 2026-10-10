import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.DiagonalResolution

namespace OAI

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution

noncomputable def row (p : SimplexCategory) : SimplicialObject (D ⥤ A) where
  obj q := free (p,q.unop)
  map f := pre (Prod.mkHom (𝟙 p) f.unop)
  map_id q := by simpa only [unop_id,←prod_id] using pre_id (p,q.unop)
  map_comp f g := by
    simpa only [prod_comp, Prod.mkHom, unop_comp, Category.id_comp] using
      pre_comp (Prod.mkHom (𝟙 p) g.unop) (Prod.mkHom (𝟙 p) f.unop)

noncomputable def rowMap {p p' : SimplexCategory} (f : p ⟶ p') : row p' ⟶ row p where
  app q := pre (Prod.mkHom f (𝟙 q.unop))
  naturality q q' g := by
    dsimp [row]
    rw [←pre_comp,←pre_comp]
    congr 1

noncomputable def chains : SimplicialObject (SimplicialObject (D ⥤ A)) where
  obj p := row p.unop
  map f := rowMap f.unop
  map_id p := by
    apply NatTrans.ext
    funext q
    dsimp [rowMap]
    simpa only [unop_id,←prod_id,row] using pre_id (p.unop,q.unop)
  map_comp f g := by
    apply NatTrans.ext
    funext q
    dsimp [rowMap, row]
    simpa only [prod_comp,Prod.mkHom,unop_comp,Category.id_comp] using
      pre_comp (Prod.mkHom g.unop (𝟙 q.unop)) (Prod.mkHom f.unop (𝟙 q.unop))

noncomputable def complex : HomologicalComplex₂ (D ⥤ A) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  AlternatingFaceMapComplex.obj (chains ⋙ alternatingFaceMapComplex (D ⥤ A))

noncomputable def total : ChainComplex (D ⥤ A) ℕ := complex.total (ComplexShape.down ℕ)

instance projective (n : ℕ) : Projective (total.X n) := by
  change Projective (∐ (fun ij : {ij : ℕ × ℕ // ij.1+ij.2=n} => free (⦋ij.1.1⦌,⦋ij.1.2⦌)))
  have (ij : {ij : ℕ × ℕ // ij.1+ij.2=n}) : Projective (free (⦋ij.1.1⦌,⦋ij.1.2⦌)) :=
    (evaluationAdjunctionRight A _).map_projective Z inferInstance
  infer_instance

noncomputable def rowAt (d : D) (p : SimplexCategory) : SimplicialObject A :=
  row p ⋙ (evaluation D A).obj d

noncomputable def chainsAt (d : D) : SimplicialObject (SimplicialObject A) :=
  chains ⋙ (SimplicialObject.whiskering _ _).obj ((evaluation D A).obj d)

noncomputable def point (d : D) : SimplicialObject A where
  obj q := ∐ (fun _ : q.unop ⟶ d.2 => Z)
  map f := Sigma.desc (fun g => Sigma.ι (fun _ : _ ⟶ d.2 => Z) (f.unop ≫ g))
  map_id q := by apply Sigma.hom_ext; intro g; simp
  map_comp f g := by apply Sigma.hom_ext; intro h; simp [Category.assoc]

@[simp] lemma chainsAt_obj_map (d : D) (p : SimplexCategoryᵒᵖ)
    {q q' : SimplexCategoryᵒᵖ} (f : q ⟶ q') :
    ((chainsAt d).obj p).map f = (pre (Prod.mkHom (𝟙 p.unop) f.unop)).app d := rfl
@[simp] lemma chainsAt_map_app (d : D) {p p' : SimplexCategoryᵒᵖ} (f : p ⟶ p')
    (q : SimplexCategoryᵒᵖ) :
    ((chainsAt d).map f).app q = (pre (Prod.mkHom f.unop (𝟙 q.unop))).app d := rfl
noncomputable def augmentation (d : D) : chainsAt d ⟶ (SimplicialObject.const _).obj (point d) where
  app p :=
    { app q := Sigma.desc (fun f : (p.unop,q.unop) ⟶ d => Sigma.ι (fun _ : q.unop ⟶ d.2 => Z) f.2)
      naturality q q' f := by
        apply Sigma.hom_ext
        intro g
        simp [point,pre]
        erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
          Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] }
  naturality p p' f := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro g
    simp [pre]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    rfl

noncomputable def augmentedAt (d : D) : SimplicialObject.Augmented (SimplicialObject A) where
  left := chainsAt d
  right := point d
  hom := augmentation d
noncomputable def section_ (d : D) : point d ⟶ (chainsAt d).obj (op ⦋0⦌) where
  app q := Sigma.desc (fun f : q.unop ⟶ d.2 =>
    Sigma.ι (fun _ : (⦋0⦌,q.unop) ⟶ d => Z) (zeroSimplex d.1,f))
  naturality q q' f := by
    apply Sigma.hom_ext
    intro g
    simp [point,pre]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    rfl

open SSet.Augmented.StandardSimplex in
noncomputable def shift_ (d : D) (n : ℕ) :
    (chainsAt d).obj (op ⦋n⦌) ⟶ (chainsAt d).obj (op ⦋n+1⦌) where
  app q := Sigma.desc (fun f : (⦋n⦌,q.unop) ⟶ d =>
    Sigma.ι (fun _ : (⦋n+1⦌,q.unop) ⟶ d => Z) (shift f.1,f.2))
  naturality q q' f := by
    apply Sigma.hom_ext
    intro g
    simp [pre]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
noncomputable def extra (d : D) : (augmentedAt d).ExtraDegeneracy where
  s' := section_ d
  s := shift_ d
  s'_comp_ε := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.comp_id]
  s₀_comp_δ₁ := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    simp only [shift_δ₁]
    rfl
  s_comp_δ₀ n := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    simp only [shift_δ₀, Prod.eta]
    exact (Category.comp_id _).symm
  s_comp_δ n i := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    simp only [shift_δ_succ]
    rfl
  s_comp_σ n i := by
    apply NatTrans.ext
    funext q
    apply Sigma.hom_ext
    intro f
    dsimp only [augmentedAt,section_,shift_,augmentation,SimplicialObject.δ,SimplicialObject.σ,NatTrans.comp_app,NatTrans.id_app]
    simp only [Quiver.Hom.unop_op, chainsAt_map_app, pre, prod_comp, Prod.mkHom, Category.id_comp]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    simp only [shift_σ_succ]
    rfl

end BiResolution

end OAI
