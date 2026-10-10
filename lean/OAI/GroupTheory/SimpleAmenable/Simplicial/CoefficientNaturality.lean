import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ExactShapeHomology
import OAI.GroupTheory.SimpleAmenable.Simplicial.CoefficientNerve

namespace OAI

namespace CoefficientNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite

private lemma comp_pair {V : Type*} [Category V] {A B C D E F : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {b : E ⟶ F} {k : F ⟶ D}
    (h₁ : i ≫ f = a ≫ j) (h₂ : j ≫ g = b ≫ k) :
    i ≫ f ≫ g = (a ≫ b) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private lemma square_of_components {V : Type*} [Category V] {A B C D E F : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {k : E ⟶ D} {h : B ⟶ F} {l : A ⟶ F} {q : F ⟶ D}
    (hf : i ≫ f = a ≫ j) (hg : j ≫ g = k)
    (hh : i ≫ h = l) (hq : a ≫ k = l ≫ q) :
    i ≫ f ≫ g = i ≫ h ≫ q := by
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc, hh, hq]

private lemma iso_transport_cancel {V : Type*} [Category V] {A B C D : V}
    (a : A ≅ B) (b : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f = a.hom ≫ g ≫ b.inv) : f ≫ b.hom = a.hom ≫ g := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section

variable {R:Type} [CommRing R] {C:Type} [Category.{0} C]
variable {F G H:C ⥤ ModuleCat.{0} R}
noncomputable def mapNat (η:F⟶G) : simplicial F ⟶ simplicial G where
  app n := desc F (fun s=>η.app s.right.unop ≫ single G s)
  naturality n m f := by
    apply hom_ext; intro s
    dsimp only [simplicial]
    rw [single_map_assoc,single_desc,single_desc_assoc,Category.assoc,single_map,
      ←Category.assoc,η.naturality,Category.assoc]
@[reassoc (attr:=simp)] lemma single_mapNat (η:F⟶G) {n:ℕ} (s:Simplex C n) :
    single F s ≫ (mapNat η).app (op ⦋n⦌)=η.app s.right.unop ≫ single G s := single_desc _ _ _
lemma mapNat_id (F:C ⥤ ModuleCat.{0} R) : mapNat (𝟙 F)=𝟙 (simplicial F) := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  simp only [mapNat,single_desc,NatTrans.id_app]
  exact (Category.comp_id (single F s)).symm
lemma mapNat_comp (η:F⟶G) (θ:G⟶H) : mapNat (η≫θ)=mapNat η ≫ mapNat θ := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  simp only [mapNat,single_desc,NatTrans.comp_app]
  change (η.app s.right.unop ≫ θ.app s.right.unop) ≫ single H s =
    single F s ≫ (mapNat η).app n ≫ (mapNat θ).app n
  exact (comp_pair (single_desc F _ s) (single_desc G _ s)).symm
variable {D:Type} [Category.{0} D] (u:C ⥤ D) (G H:D ⥤ ModuleCat.{0} R) (η:G⟶H)
lemma post_natural : mapNat (Functor.whiskerLeft u η) ≫ post u H=post u G ≫ mapNat η := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single (u ⋙ G) s ≫ (mapNat (Functor.whiskerLeft u η)).app n ≫ (post u H).app n =
    single (u ⋙ G) s ≫ (post u G).app n ≫ (mapNat η).app n
  exact square_of_components (single_desc (u ⋙ G) _ s)
    (single_desc (u ⋙ H) _ s) (single_desc (u ⋙ G) _ s)
    (single_desc G (fun z => η.app z.right.unop ≫ single H z) (s ⋙ u.op)).symm
end

variable {C:Type} [Category.{0} C]
noncomputable def functor : (C ⥤ ModuleCat.{0} ℤ) ⥤ SimplicialObject (ModuleCat.{0} ℤ) where
  obj := simplicial
  map := mapNat
  map_id := mapNat_id
  map_comp := mapNat_comp
noncomputable instance : (functor (C:=C)).Additive where
  map_add := by
    intro F G η θ
    apply NatTrans.ext; funext n
    apply hom_ext; intro s
    simp only [functor,mapNat,single_desc]
    erw [NatTrans.app_add, Preadditive.comp_add, single_desc, single_desc, Preadditive.add_comp]
noncomputable def vertices (n:ℕ) : Discrete (Simplex C n) ⥤ C :=
  Discrete.functor (fun s=>s.right.unop)
noncomputable def degree (n:ℕ) : (C ⥤ ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ :=
  functor ⋙ (evaluation _ _).obj (op ⦋n⦌)
noncomputable def vertexCocone (F:C ⥤ ModuleCat.{0} ℤ) (n:ℕ) : Cocone (vertices n ⋙ F) where
  pt := Obj F n
  ι := Discrete.natTrans (fun s=>single F s.as)
noncomputable def vertexIsColimit (F:C ⥤ ModuleCat.{0} ℤ) (n:ℕ) : IsColimit (vertexCocone F n) where
  desc d := desc F (fun s=>d.ι.app ⟨s⟩)
  fac _ _ := single_desc _ _ _
  uniq d _ h := hom_ext F (fun s=> (h ⟨s⟩).trans (single_desc F (fun s=>d.ι.app ⟨s⟩) s).symm)
noncomputable def degreeIso (n:ℕ) : degree (C:=C) n ≅
    (Functor.whiskeringLeft (Discrete (Simplex C n)) C (ModuleCat.{0} ℤ)).obj (vertices n) ⋙ colim :=
  NatIso.ofComponents (fun F=>(vertexIsColimit F n).coconePointUniqueUpToIso (colimit.isColimit _)) (by
    intro F G η
    apply hom_ext; intro s
    change single F s ≫ (mapNat η).app (op ⦋n⦌) ≫ _ = _
    have hg := (vertexIsColimit G n).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨s⟩
    have hf := (vertexIsColimit F n).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨s⟩
    change single G s ≫ _ = colimit.ι (vertices n ⋙ G) ⟨s⟩ at hg
    change single F s ≫ _ = colimit.ι (vertices n ⋙ F) ⟨s⟩ at hf
    exact square_of_components (single_mapNat η s) hg hf
      (colimit.ι_map (Functor.whiskerLeft (vertices n) η) ⟨s⟩).symm)
noncomputable instance degree_preservesLimits (n:ℕ) : PreservesFiniteLimits (degree (C:=C) n) :=
  preservesFiniteLimits_of_natIso (degreeIso n).symm
noncomputable instance degree_preservesColimits (n:ℕ) : PreservesColimits (degree (C:=C) n) :=
  preservesColimits_of_natIso (degreeIso n).symm
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
open ExactShapeHomology

variable {C:Type} [Category.{0} C]
noncomputable def levelMap {m n:ℕ} (f:⦋m⦌⟶⦋n⦌) : degree (C:=C) n ⟶ degree m where
  app F := (simplicial F).map f.op
  naturality _ _ η := ((mapNat η).naturality f.op).symm
lemma levelMap_id (n:ℕ) : levelMap (C:=C) (𝟙 ⦋n⦌)=𝟙 _ := by
  apply NatTrans.ext; funext F
  exact (simplicial F).map_id _
lemma levelMap_comp {l m n:ℕ} (f:⦋l⦌⟶⦋m⦌) (g:⦋m⦌⟶⦋n⦌) :
    levelMap (C:=C) (f≫g)=levelMap g ≫ levelMap f := by
  apply NatTrans.ext; funext F
  exact (simplicial F).map_comp g.op f.op
noncomputable def chainSimplicial (L:ChainComplex (C ⥤ A) ℕ) :
    SimplicialObject (ChainComplex A ℕ) where
  obj p := ((degree p.unop.len).mapHomologicalComplex c).obj L
  map f := (NatTrans.mapHomologicalComplex (levelMap f.unop) c).app L
  map_id p := by
    apply HomologicalComplex.Hom.ext; funext q
    exact congrArg (fun η=>(η.app (L.X q))) (levelMap_id p.unop.len)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext; funext q
    exact congrArg (fun η=>(η.app (L.X q))) (levelMap_comp g.unop f.unop)
noncomputable def chainSimplicialHomology (L:ChainComplex (C ⥤ A) ℕ) (q:ℕ) :
    chainSimplicial L ⋙ homologyFunctor A c q ≅ simplicial (L.homology q) :=
  NatIso.ofComponents (fun p=>(L.sc q).mapHomologyIso (degree p.unop.len)) (by
    intro p r f
    have h:=ShortComplex.homologyMap_mapNatTrans (L.sc q) (levelMap (C:=C) f.unop)
    change homologyMap ((chainSimplicial L).map f) q =
      ((L.sc q).mapHomologyIso (degree p.unop.len)).hom ≫
        (simplicial (L.homology q)).map f ≫
          ((L.sc q).mapHomologyIso (degree r.unop.len)).inv at h
    change homologyMap ((chainSimplicial L).map f) q ≫ _ = _
    exact iso_transport_cancel _ _ _ _ h)
noncomputable def double (L:ChainComplex (C ⥤ A) ℕ) :
    HomologicalComplex₂ A c c := (alternatingFaceMapComplex _).obj (chainSimplicial L)
noncomputable def rowIso (L:ChainComplex (C ⥤ A) ℕ) (q:ℕ) :
    TotalFiniteness.row (double L) q ≅ complex (L.homology q) := by
  exact eqToIso (congrArg (fun T => T.obj (chainSimplicial L))
    (map_alternatingFaceMapComplex (homologyFunctor A c q))) ≪≫
      (alternatingFaceMapComplex A).mapIso (chainSimplicialHomology L q)
end

end CoefficientNerve

end OAI
