import Mathlib
import OAI.CategoryTheory.Thomason.SkeletalCategories

namespace OAI

/-! Subdivision Faces. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E]

def tableStart (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.sourceObject x)

def tableFinish (x : Table (complex E)) : E :=
  tableObjectsEquiv ((complex E).nu.targetObject x)

lemma tableStart_row (x : Table (complex E)) :
    (x.row 0 false).val = bracket [tableStart x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.sourceObject x))
  exact he.symm

lemma tableFinish_row (x : Table (complex E)) :
    (x.row 0 true).val = bracket [tableFinish x] := by
  have he := congrArg (fun a : (complex E).nu.Objects => (a.val.row 0 false).val)
    (tableObjectsEquiv.symm_apply_apply ((complex E).nu.targetObject x))
  exact he.symm

lemma tableStart_le_finish (x : Table (complex E)) : tableStart x ≤ tableFinish x :=
  table_source_le_target x _ _ (tableStart_row x) (tableFinish_row x)

lemma map_table_eq_edge {D : OmegaCategory.{v}} (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) (x : Table (complex E)) :
    F.map x = F.map (edgeTable (tableStart x) (tableFinish x) (tableStart_le_finish x)) := by
  have hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici (tableStart x)) := by
    apply table_supportedOn_upper (by intro a b hab ha; exact le_trans ha hab) x
    intro b
    cases b
    · rw [tableStart_row]; exact bracket_mem_supportedOn (by simp)
    · rw [tableFinish_row]
      exact bracket_mem_supportedOn (by simpa using tableStart_le_finish x)
  let y := coneTable (tableStart x) x hx
  have hs : (complex E).nu.source 1 y =
      edgeTable (tableStart x) (tableFinish x) (tableStart_le_finish x) :=
    coneTable_one_source x _ _ (tableStart_row x) (tableFinish_row x) hx
  have ht : (complex E).nu.target 1 y = (complex E).nu.target 1 x :=
    coneTable_one_target x _ (tableStart_row x) hx
  calc
    F.map x = D.target 1 (F.map x) := (D.target_eq_self_of_source_eq_self (hD _)).symm
    _ = F.map ((complex E).nu.target 1 x) := (F.map_target 1 x).symm
    _ = F.map ((complex E).nu.target 1 y) := congrArg F.map ht.symm
    _ = D.target 1 (F.map y) := F.map_target 1 y
    _ = F.map y := D.target_eq_self_of_source_eq_self (hD _)
    _ = D.source 1 (F.map y) := (hD _).symm
    _ = F.map ((complex E).nu.source 1 y) := (F.map_source 1 y).symm
    _ = _ := congrArg F.map hs

lemma ordered_arrow_ext (f g : Arrow E) (hl : f.left = g.left) (hr : f.right = g.right) :
    f = g := Arrow.ext hl hr (Subsingleton.elim _ _)

def tableEndpoints : OmegaCategory.Functor (complex E).nu (ofCategory E) where
  map x := Arrow.mk (homOfLE (tableStart_le_finish x))
  map_source k x := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.source, tableStart]
    · cases k <;> simp [ofCategory, CategoryCell.source, tableStart, tableFinish]
  map_target k x := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.target, tableStart, tableFinish]
    · cases k <;> simp [ofCategory, CategoryCell.target, tableFinish]
  map_comp k x y h h' := by
    apply ordered_arrow_ext
    · cases k <;> simp [ofCategory, CategoryCell.comp, tableStart]
    · cases k with
      | zero => simp [ofCategory, CategoryCell.comp, tableFinish]
      | succ k =>
        have he := congrArg (fun z => tableObjectsEquiv ((complex E).nu.targetObject z)) h
        simpa [ofCategory, CategoryCell.comp, tableFinish] using he.symm

@[simp] lemma tableStart_edge (a b : E) (hab : a ≤ b) :
    tableStart (edgeTable a b hab) = a := by
  simp [tableStart, edgeTable_sourceObject]

@[simp] lemma tableFinish_edge (a b : E) (hab : a ≤ b) :
    tableFinish (edgeTable a b hab) = b := by
  simp [tableFinish, edgeTable_targetObject]

lemma edgeTable_diagonal (a : E) : edgeTable a a le_rfl = vertexTable a := by
  ext p b
  cases p with
  | zero => cases b <;> rfl
  | succ p =>
    cases p with
    | zero =>
      apply Subtype.ext
      change bracket [a,a] = 0
      exact bracket_of_not_pairwise (by simp)
    | succ p => rfl

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E] {D : OmegaCategory.{v}}

def orientalOneFunctor (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) : E ⥤ D.OneSkeleton where
  obj a := F.objects (tableObjectsEquiv.symm a)
  map {a b} f := ⟨F.map (edgeTable a b (leOfHom f)), hD _, by
      exact (F.map_source 0 _).symm.trans
        (congrArg F.map (edgeTable_source a b (leOfHom f))), by
      exact (F.map_target 0 _).symm.trans
        (congrArg F.map (edgeTable_target a b (leOfHom f)))⟩
  map_id a := by
    apply Subtype.ext
    exact congrArg F.map (edgeTable_diagonal a)
  map_comp {a b c} f g := by
    apply Subtype.ext
    let x := edgeTable a b (leOfHom f)
    let y := edgeTable b c (leOfHom g)
    have hxy : (complex E).nu.target 0 x = (complex E).nu.source 0 y :=
      (edgeTable_target a b _).trans (edgeTable_source b c _).symm
    let z := (complex E).nu.comp 0 x y hxy
    have hs : tableStart z = a := by
      exact (congrArg tableObjectsEquiv ((complex E).nu.sourceObject_comp 0 x y hxy)).trans
        (tableStart_edge a b _)
    have ht : tableFinish z = c := by
      exact (congrArg tableObjectsEquiv ((complex E).nu.targetObject_comp 0 x y hxy)).trans
        (tableFinish_edge b c _)
    have he := map_table_eq_edge hD F z
    have he' : F.map z = F.map (edgeTable a c (leOfHom (f ≫ g))) := by
      simpa only [hs, ht] using he
    exact he'.symm.trans (F.map_comp 0 x y hxy _)

def ordinalDiagramFunctor (G : E ⥤ D.OneSkeleton) :
    OmegaCategory.Functor (complex E).nu D :=
  OmegaCategory.Functor.comp tableEndpoints
    (OmegaCategory.Functor.comp (ofCategoryMap G) D.oneSkeletonEvaluation)

lemma ordinalDiagramFunctor_orientalOneFunctor (hD : D.IsTruncated 1)
    (F : OmegaCategory.Functor (complex E).nu D) :
    ordinalDiagramFunctor (orientalOneFunctor hD F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact (map_table_eq_edge hD F x).symm

@[simp] lemma tableStart_vertex (a : E) : tableStart (vertexTable a) = a := by
  have he := tableStart_edge a a le_rfl
  rwa [edgeTable_diagonal] at he

@[simp] lemma tableFinish_vertex (a : E) : tableFinish (vertexTable a) = a := by
  have he := tableFinish_edge a a le_rfl
  rwa [edgeTable_diagonal] at he

lemma tableEndpoints_vertex (a : E) : tableEndpoints.map (vertexTable a) = Arrow.mk (𝟙 a) := by
  apply ordered_arrow_ext
  · exact tableStart_vertex a
  · exact tableFinish_vertex a

lemma tableEndpoints_edge (a b : E) (hab : a ≤ b) :
    tableEndpoints.map (edgeTable a b hab) = Arrow.mk (homOfLE hab) := by
  apply ordered_arrow_ext
  · exact tableStart_edge a b hab
  · exact tableFinish_edge a b hab

lemma orientalOneFunctor_ordinalDiagramFunctor_obj (hD : D.IsTruncated 1)
    (G : E ⥤ D.OneSkeleton) (a : E) :
    (orientalOneFunctor hD (ordinalDiagramFunctor G)).obj a = G.obj a := by
  apply Subtype.ext
  change D.oneSkeletonEvaluation.map
    ((ofCategoryMap G).map (tableEndpoints.map (vertexTable a))) = _
  rw [tableEndpoints_vertex]
  change (G.map (𝟙 a)).val = _
  rw [G.map_id]
  rfl

lemma orientalOneFunctor_ordinalDiagramFunctor (hD : D.IsTruncated 1)
    (G : E ⥤ D.OneSkeleton) : orientalOneFunctor hD (ordinalDiagramFunctor G) = G := by
  refine CategoryTheory.Functor.ext
    (orientalOneFunctor_ordinalDiagramFunctor_obj hD G) ?_
  intro a b f
  apply Subtype.ext
  change D.oneSkeletonEvaluation.map
    ((ofCategoryMap G).map (tableEndpoints.map (edgeTable a b (leOfHom f)))) = _
  rw [tableEndpoints_edge]
  change (G.map (homOfLE (leOfHom f))).val = _
  have he : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  rw [he]
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]

def orientalOneEquiv (hD : D.IsTruncated 1) :
    OmegaCategory.Functor (complex E).nu D ≃ (E ⥤ D.OneSkeleton) where
  toFun := orientalOneFunctor hD
  invFun := ordinalDiagramFunctor
  left_inv := ordinalDiagramFunctor_orientalOneFunctor hD
  right_inv := orientalOneFunctor_ordinalDiagramFunctor hD

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E] {B : Type v} [LinearOrder B]
  {D : OmegaCategory.{w}}

lemma complexMap_vertex (f : E →o B) (a : E) :
    (complexMap f).nu.map (vertexTable a) = vertexTable (f a) := by
  change (complexMap f).table (vertexTable a) = _
  ext p b
  apply Subtype.ext
  cases p with
  | zero =>
    change map f (bracket [a]) = bracket [f a]
    simpa using map_bracket f (by simp : [a].Pairwise (· ≤ ·))
  | succ p => exact map_zero (map f)

lemma complexMap_edge (f : E →o B) (a b : E) (hab : a ≤ b) :
    (complexMap f).nu.map (edgeTable a b hab) = edgeTable (f a) (f b) (f.monotone hab) := by
  change (complexMap f).table (edgeTable a b hab) = _
  ext p e
  apply Subtype.ext
  cases p with
  | zero =>
    cases e <;>
      change map f (bracket [_]) = bracket [f _] <;>
      simpa using map_bracket f (by simp : [_].Pairwise (· ≤ ·))
  | succ p =>
    cases p with
    | zero =>
      change map f (bracket [a,b]) = bracket [f a, f b]
      simpa using map_bracket f (by simpa using hab : [a,b].Pairwise (· ≤ ·))
    | succ p => exact map_zero (map f)

lemma orientalOneFunctor_naturality_obj (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) (a : E) :
    (orientalOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F)).obj a =
      (f.monotone.functor ⋙ orientalOneFunctor hD F).obj a := by
  apply Subtype.ext
  exact congrArg F.map (complexMap_vertex f a)

lemma orientalOneFunctor_naturality (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) :
    orientalOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F) =
      f.monotone.functor ⋙ orientalOneFunctor hD F := by
  refine CategoryTheory.Functor.ext (orientalOneFunctor_naturality_obj hD f F) ?_
  intro a b g
  apply Subtype.ext
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]
  exact congrArg F.map (complexMap_edge f a b (leOfHom g))

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite NormalizedChains

def oneNerveIso {D : OmegaCategory.{u}} (hD : D.IsTruncated 1) :
    streetNerve D ≅ nerve D.OneSkeleton :=
  NatIso.ofComponents
    (fun m => Equiv.toIso (orientalOneEquiv (E := Fin (m.unop.len+1)) hD)) (by
      intro m n f
      apply ConcreteCategory.hom_ext
      intro F
      exact orientalOneFunctor_naturality hD f.unop.toOrderHom F)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}

def oneCell (hC : C.IsTruncated 1) (x : C.Cell) :
    @Quiver.Hom C.OneSkeleton (inferInstance : Quiver C.OneSkeleton)
      (C.sourceObject x) (C.targetObject x) := ⟨x, hC x, rfl, rfl⟩

lemma oneSkeletonIso_inv_map (hC : C.IsTruncated 1) (x : C.Cell) :
    (oneSkeletonIso hC).inv.map x = Arrow.mk (oneCell hC x) := by
  apply C.oneSkeletonEvaluation_injective
  exact congrArg (fun F : OmegaCategory.Functor C C => F.map x)
    (oneSkeletonIso hC).inv_hom_id

def liftOneFunctor (hC : C.IsTruncated 1) (G : C.OneSkeleton ⥤ D.OneSkeleton) :
    OmegaCategory.Functor C D :=
  OmegaCategory.Functor.comp (oneSkeletonIso hC).inv
    (OmegaCategory.Functor.comp (ofCategoryMap G) D.oneSkeletonEvaluation)

lemma liftOneFunctor_map (hC : C.IsTruncated 1) (G : C.OneSkeleton ⥤ D.OneSkeleton)
    (x : C.Cell) : (liftOneFunctor hC G).map x = (G.map (oneCell hC x)).val := by
  change ((ofCategoryMap G).map ((oneSkeletonIso hC).inv.map x)).hom.val = _
  rw [oneSkeletonIso_inv_map]
  rfl

lemma liftOneFunctor_oneMap (hC : C.IsTruncated 1) (F : OmegaCategory.Functor C D) :
    liftOneFunctor hC F.oneMap = F := by
  ext x
  exact liftOneFunctor_map hC F.oneMap x

lemma mappedCast_val (G : C.OneSkeleton ⥤ D.OneSkeleton) {a a' b b' : C.OneSkeleton}
    (hs : a' = a) (ht : b = b') (f : a ⟶ b) :
    (G.map (eqToHom hs ≫ f ≫ eqToHom ht)).val = (G.map f).val := by
  rw [G.map_comp, G.map_comp, eqToHom_map, eqToHom_map]
  simp only [one_eqToHom_comp_val, one_comp_eqToHom_val]

lemma oneMap_liftOneFunctor_obj (hC : C.IsTruncated 1)
    (G : C.OneSkeleton ⥤ D.OneSkeleton) (a : C.OneSkeleton) :
    (liftOneFunctor hC G).oneMap.obj a = G.obj a := by
  apply Subtype.ext
  change (liftOneFunctor hC G).map a.val = (G.obj a).val
  refine (liftOneFunctor_map hC G a.val).trans ?_
  have hs : (C.sourceObject a.val : C.OneSkeleton) = a := Subtype.ext a.property
  have ht : (C.targetObject a.val : C.OneSkeleton) = a :=
    Subtype.ext (C.target_eq_self_of_source_eq_self a.property)
  have h : oneCell hC a.val =
      (@eqToHom C.OneSkeleton (inferInstance) _ _ hs) ≫ 𝟙 a ≫
        (@eqToHom C.OneSkeleton (inferInstance) _ _ ht.symm) := by
    apply Subtype.ext
    exact ((one_eqToHom_comp_val hs _).trans
      (one_comp_eqToHom_val (𝟙 a) ht.symm)).symm
  exact (congrArg (fun q => (G.map q).val) h).trans
    ((mappedCast_val G hs ht.symm (𝟙 a)).trans
      (congrArg (fun q : G.obj a ⟶ G.obj a => q.val) (G.map_id a)))

lemma oneMap_liftOneFunctor (hC : C.IsTruncated 1)
    (G : C.OneSkeleton ⥤ D.OneSkeleton) : (liftOneFunctor hC G).oneMap = G := by
  refine CategoryTheory.Functor.ext (oneMap_liftOneFunctor_obj hC G) ?_
  intro a b f
  apply Subtype.ext
  change (liftOneFunctor hC G).map f.val = _
  refine (liftOneFunctor_map hC G f.val).trans ?_
  have hs : (C.sourceObject f.val : C.OneSkeleton) = a := Subtype.ext f.property.2.1
  have ht : (C.targetObject f.val : C.OneSkeleton) = b := Subtype.ext f.property.2.2
  have h : oneCell hC f.val =
      (@eqToHom C.OneSkeleton (inferInstance) _ _ hs) ≫ f ≫
        (@eqToHom C.OneSkeleton (inferInstance) _ _ ht.symm) := by
    apply Subtype.ext
    exact ((one_eqToHom_comp_val hs _).trans (one_comp_eqToHom_val f ht.symm)).symm
  exact ((congrArg (fun q => (G.map q).val) h).trans (mappedCast_val G hs ht.symm f)).trans
    ((one_eqToHom_comp_val _ _).trans (one_comp_eqToHom_val _ _)).symm

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def oneSkeletonCatFunctor : NCategory.{u} 1 ⥤ Cat.{u,u} where
  obj C := Cat.of C.val.OneSkeleton
  map F := F.oneMap.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def oneSkeletonFullyFaithful : oneSkeletonCatFunctor.{u}.FullyFaithful where
  preimage {C D} F := liftOneFunctor C.property F.toFunctor
  map_preimage {C D} F := by
    apply Cat.Hom.ext
    exact oneMap_liftOneFunctor C.property F.toFunctor
  preimage_map {C D} F := liftOneFunctor_oneMap C.property F

instance : oneSkeletonCatFunctor.{u}.Full := oneSkeletonFullyFaithful.full
instance : oneSkeletonCatFunctor.{u}.Faithful := oneSkeletonFullyFaithful.faithful

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory Opposite

lemma oneNerveIso_natural {C D : OmegaCategory.{u}} (hC : C.IsTruncated 1)
    (hD : D.IsTruncated 1) (F : OmegaCategory.Functor C D) :
    streetNerveMap F ≫ (oneNerveIso hD).hom =
      (oneNerveIso hC).hom ≫ nerveMap F.oneMap := by
  ext m x
  rfl

def oneNerveFunctorIso : streetNerveFinite.{u} 1 ≅
    oneSkeletonCatFunctor ⋙ nerveFunctor :=
  NatIso.ofComponents (fun C => oneNerveIso C.property) (by
    intro C D F
    exact oneNerveIso_natural C.property D.property F)

instance streetNerveFiniteOne_full : (streetNerveFinite.{u} 1).Full :=
  CategoryTheory.Functor.Full.of_iso oneNerveFunctorIso.symm

instance streetNerveFiniteOne_faithful : (streetNerveFinite.{u} 1).Faithful :=
  CategoryTheory.Functor.Faithful.of_iso oneNerveFunctorIso.symm

instance categorificationFiniteOne_counit_iso :
    IsIso (categorificationFiniteAdjunction.{u} 1).counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

noncomputable def categorificationFiniteOne_nerve_iso (C : NCategory.{u} 1) :
    (categorificationFinite 1).obj ((streetNerveFinite 1).obj C) ≅ C :=
  asIso ((categorificationFiniteAdjunction 1).counit.app C)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

abbrev OrdinalVertices (n : ℕ) := SimplexCategory.toPartOrd.{u}.obj ⦋n⦌
local instance (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))
abbrev OrdinalChains (n : ℕ) := NonemptyFiniteChains (OrdinalVertices.{u} n)
def ordinalVertex (n : ℕ) (i : Fin (n + 1)) : OrdinalVertices.{u} n := ULift.up i

lemma le_initialFlag (n : ℕ) (s : OrdinalChains.{u} n) (a : OrdinalVertices.{u} n) :
    s ≤ initialFlag ⦋n⦌ a ↔ chainLast s ≤ a := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp (h (chainGreatest_mem s))).2
  · intro h x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (le_chainGreatest s hx).trans h⟩

noncomputable def partialLastVertex (n : ℕ) (k : OrdinalVertices.{u} n) :
    OrdinalChains.{u} n →o OrdinalChains.{u} n := by
  exact {
    toFun := fun s => if chainLast s ≤ k then s else initialFlag ⦋n⦌ (chainLast s)
    monotone' := by
      intro s t h
      have hst : chainLast s ≤ chainLast t := chainLast.monotone h
      by_cases hs : chainLast s ≤ k
      · by_cases ht : chainLast t ≤ k
        · simpa only [ite_eq_left hs, ite_eq_left ht] using h
        · simpa only [ite_eq_left hs, ite_eq_right ht] using (le_initialFlag n s (chainLast t)).2 hst
      · have ht : ¬chainLast t ≤ k := fun ht => hs (hst.trans ht)
        simpa only [ite_eq_right hs, ite_eq_right ht] using (initialFlag ⦋n⦌).monotone hst }

lemma partialLastVertex_apply (n : ℕ) (k : OrdinalVertices.{u} n)
    (s : OrdinalChains.{u} n) : partialLastVertex n k s =
      if chainLast s ≤ k then s else initialFlag ⦋n⦌ (chainLast s) := rfl

lemma chainLast_partialLastVertex (n : ℕ) (k : OrdinalVertices.{u} n)
    (s : OrdinalChains.{u} n) : chainLast (partialLastVertex n k s) = chainLast s := by
  rw [partialLastVertex_apply]
  split_ifs with h
  · rfl
  · exact chainLast_initialFlag _ _

lemma partialLastVertex_initialFlag (n : ℕ) (k a : OrdinalVertices.{u} n) :
    partialLastVertex n k (initialFlag ⦋n⦌ a) = initialFlag ⦋n⦌ a := by
  rw [partialLastVertex_apply, chainLast_initialFlag]
  split_ifs <;> rfl

lemma partialLastVertex_comp_of_le (n : ℕ) (j k : OrdinalVertices.{u} n) (hjk : j ≤ k) :
    (partialLastVertex n j).comp (partialLastVertex n k) = partialLastVertex n j := by
  apply OrderHom.ext
  funext s
  change partialLastVertex n j (partialLastVertex n k s) = _
  rw [partialLastVertex_apply n k]
  split_ifs with h
  · rfl
  · rw [partialLastVertex_initialFlag, partialLastVertex_apply,
      ite_eq_right (fun hj => h (hj.trans hjk))]

lemma partialLastVertex_comm (n : ℕ) (j k : OrdinalVertices.{u} n) :
    (partialLastVertex n j).comp (partialLastVertex n k) =
      (partialLastVertex n k).comp (partialLastVertex n j) := by
  apply OrderHom.ext
  funext s
  change partialLastVertex n j (partialLastVertex n k s) =
    partialLastVertex n k (partialLastVertex n j s)
  by_cases hj : chainLast s ≤ j <;> by_cases hk : chainLast s ≤ k <;>
    simp only [partialLastVertex_apply, hj, hk,
      ite_true, ite_false, chainLast_initialFlag]

lemma partialLastVertex_idem (n : ℕ) (k : OrdinalVertices.{u} n) :
    (partialLastVertex n k).comp (partialLastVertex n k) = partialLastVertex n k :=
  partialLastVertex_comp_of_le n k k le_rfl

lemma partialLastVertex_top (n : ℕ) :
    partialLastVertex.{u} n ⟨Fin.last n⟩ = OrderHom.id := by
  apply OrderHom.ext
  funext s
  exact ite_eq_left (show (chainLast s).down ≤ Fin.last n from Fin.le_last _)

lemma partialLastVertex_zero (n : ℕ) (s : OrdinalChains.{u} n) :
    partialLastVertex.{u} n (ordinalVertex n 0) s = initialFlag ⦋n⦌ (chainLast s) := by
  rw [partialLastVertex_apply]
  split_ifs with h
  · apply le_antisymm
    · exact (le_initialFlag n s _).2 le_rfl
    · intro x hx
      have hx' : x ≤ chainLast s := (Finset.mem_filter.mp hx).2
      have hzero : chainLast s = ⟨(0 : Fin (n + 1))⟩ := by
        apply ULift.ext
        exact le_antisymm h (Fin.zero_le _)
      have hxzero : x = chainLast s := by
        apply ULift.ext
        exact le_antisymm hx' (by rw [hzero]; exact Fin.zero_le _)
      exact hxzero.symm ▸ chainGreatest_mem s
  · rfl

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exComparison_apply (X : SSet.{u}) (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (exComparison.app X).app (op ⦋n⦌) x =
      ULift.up (simplexLastVertex.app ⦋n⦌ ≫ SSet.yonedaEquiv.symm x) := by
  change ((SSet.sdExAdjunction.homEquiv X X) (lastVertex.app X)).app _ x = _
  erw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  congr 1
  change (SSet.stdSimplex.sdIso.app ⦋n⦌).inv ≫
    SSet.sd.map (SSet.yonedaEquiv.symm x) ≫ lastVertex.app X = _
  erw [lastVertex.naturality, lastVertex_stdSimplex]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

noncomputable def partialLastMap (n : ℕ) (k : OrdinalVertices.{u} n) :
    SimplexCategory.sd.obj ⦋n⦌ ⟶ SimplexCategory.sd.obj ⦋n⦌ :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom (partialLastVertex n k))

lemma partialLastMap_comp_of_le (n : ℕ) (j k : OrdinalVertices.{u} n) (hjk : j ≤ k) :
    partialLastMap n k ≫ partialLastMap n j = partialLastMap n j := by
  erw [partialLastMap, partialLastMap, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  exact partialLastVertex_comp_of_le n j k hjk

lemma partialLastMap_comm (n : ℕ) (j k : OrdinalVertices.{u} n) :
    partialLastMap n k ≫ partialLastMap n j = partialLastMap n j ≫ partialLastMap n k := by
  unfold partialLastMap
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  exact partialLastVertex_comm n j k

lemma partialLastMap_zero (n : ℕ) :
    partialLastMap.{u} n (ordinalVertex n 0) =
      simplexLastVertex.app ⦋n⦌ ≫ simplexLastVertexSection ⦋n⦌ := by
  have h : PartOrd.ofHom (partialLastVertex.{u} n (ordinalVertex n 0)) =
      chainLastNat.app (SimplexCategory.toPartOrd.obj ⦋n⦌) ≫
      PartOrd.ofHom (initialFlag ⦋n⦌) := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext s
    exact partialLastVertex_zero n s
  change _ = (PartOrd.nerveFunctor.map _ ≫ simplexNerveIso.inv.app _) ≫
    (simplexNerveIso.hom.app _ ≫ PartOrd.nerveFunctor.map _)
  simp only [Category.assoc]
  change PartOrd.nerveFunctor.map _ = _
  erw [h, CategoryTheory.Functor.map_comp]
  erw [← Category.assoc (simplexNerveIso.inv.app ⦋n⦌),
    simplexNerveIso.inv_hom_id_app, Category.id_comp]

def ExLevel (X : SSet.{u}) (n : ℕ) (k : OrdinalVertices.{u} n)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : Prop :=
  partialLastMap n k ≫ x.down = x.down

lemma ExLevel.mono {X : SSet.{u}} {n : ℕ} {j k : OrdinalVertices.{u} n}
    {x : (SSet.ex.obj X).obj (op ⦋n⦌)} (h : ExLevel X n j x) (hjk : j ≤ k) :
    ExLevel X n k x := by
  change partialLastMap n k ≫ x.down = _
  calc
    _ = partialLastMap n k ≫ partialLastMap n j ≫ x.down := by erw [h]
    _ = x.down := by erw [← Category.assoc, partialLastMap_comp_of_le n j k hjk]; exact h

lemma exLevel_top (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X n ⟨Fin.last n⟩ x := by
  change PartOrd.nerveFunctor.map (PartOrd.ofHom (partialLastVertex n ⟨Fin.last n⟩)) ≫ _ = _
  erw [partialLastVertex_top]
  change PartOrd.nerveFunctor.map (𝟙 _) ≫ _ = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

lemma exLevel_zero_iff (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X n (ordinalVertex n 0) x ↔
      x ∈ Set.range ((exComparison.app X).app (op ⦋n⦌)) := by
  constructor
  · intro h
    refine ⟨SSet.yonedaEquiv (simplexLastVertexSection ⦋n⦌ ≫ x.down), ?_⟩
    erw [exComparison_apply, Equiv.symm_apply_apply]
    apply ULift.ext
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.down)
      (partialLastMap_zero n).symm).trans h)
  · rintro ⟨y, rfl⟩
    change partialLastMap n (ordinalVertex n 0) ≫ _ = _
    erw [exComparison_apply]
    change partialLastMap n (ordinalVertex n 0) ≫ (simplexLastVertex.app ⦋n⦌ ≫ _) = _
    erw [partialLastMap_zero]
    simp only [Category.assoc, ← Category.assoc (simplexLastVertexSection ⦋n⦌),
      simplexLastVertexSection_comp, Category.id_comp]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

noncomputable def singletonChain {A : Type*} [PartialOrder A] (a : A) :
    NonemptyFiniteChains A := by
  classical
  exact { finset := {a}
          comparable := by
            rintro ⟨x, hx⟩ ⟨y, hy⟩
            simp only [Finset.mem_singleton] at hx hy
            subst x; subst y
            exact Or.inl le_rfl }

lemma mem_singletonChain {A : Type*} [PartialOrder A] (a x : A) :
    x ∈ (singletonChain a).finset ↔ x = a := Finset.mem_singleton

noncomputable def chainUnionMap {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) : NonemptyFiniteChains A →o NonemptyFiniteChains B := by
  classical
  exact {
    toFun s := {
      finset := s.finset.biUnion (fun a => (f a).finset)
      nonempty := by
        obtain ⟨a, ha⟩ := s.nonempty
        obtain ⟨b, hb⟩ := (f a).nonempty
        exact ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩⟩
      comparable := fun a b => le_total a.val b.val }
    monotone' s t h b hb := by
      obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨a, h ha, hb⟩ }

lemma mem_chainUnionMap {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) (s : NonemptyFiniteChains A) (b : B) :
    b ∈ (chainUnionMap f s).finset ↔ ∃ a ∈ s.finset, b ∈ (f a).finset := by
  classical
  exact Finset.mem_biUnion

lemma chainUnionMap_singleton {A : Type*} [LinearOrder A] (s : NonemptyFiniteChains A) :
    chainUnionMap singletonChain s = s := by
  apply NonemptyFiniteChains.ext
  ext a
  simp only [mem_chainUnionMap, mem_singletonChain]
  exact ⟨fun ⟨b, hb, he⟩ => he.symm ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

lemma chainUnionMap_map {A B C : Type*} [PartialOrder A] [PartialOrder B] [LinearOrder C]
    (f : B → NonemptyFiniteChains C) (g : A →o B) (s : NonemptyFiniteChains A) :
    chainUnionMap f (s.map g) = chainUnionMap (fun a => f (g a)) s := by
  apply NonemptyFiniteChains.ext
  ext c
  simp only [mem_chainUnionMap, NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ha, hc⟩
  · rintro ⟨a, ha, hc⟩
    exact ⟨g a, ⟨a, ha, rfl⟩, hc⟩

local instance (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))

noncomputable def extraVertexFace (n : ℕ) (k : Fin (n + 1)) (i : OrdinalVertices.{u} (n + 1)) :
    OrdinalChains.{u} n := by
  classical
  exact if i.down = k.succ then initialFlag ⦋n⦌ (ordinalVertex n k)
  else singletonChain (ordinalVertex n (k.predAbove i.down))

noncomputable def extraVertex (n : ℕ) (k : Fin (n + 1)) :
    OrdinalChains.{u} (n + 1) →o OrdinalChains.{u} n :=
  chainUnionMap (extraVertexFace n k)

lemma predAbove_succ_succAbove {n : ℕ} (k i : Fin (n + 1)) :
    k.predAbove (k.succ.succAbove i) = i := by
  apply Fin.succAbove_right_injective (p := k.succ)
  exact Fin.succ_succAbove_predAbove (Fin.succAbove_ne _ _)

lemma extraVertexFace_gap (n : ℕ) (k : Fin (n + 1)) (i : OrdinalVertices.{u} n) :
    extraVertexFace n k (ordinalVertex (n + 1) (k.succ.succAbove i.down)) = singletonChain i := by
  classical
  unfold extraVertexFace
  erw [ite_eq_right (Fin.succAbove_ne _ _), predAbove_succ_succAbove]
  rfl

noncomputable def faceVertices (n : ℕ) (i : Fin (n + 2)) :
    OrdinalVertices.{u} n →o OrdinalVertices.{u} (n + 1) :=
  (SimplexCategory.toPartOrd.map (SimplexCategory.δ i)).hom

lemma faceVertices_apply (n : ℕ) (i : Fin (n + 2)) (a : OrdinalVertices.{u} n) :
    faceVertices n i a = ordinalVertex (n + 1) (i.succAbove a.down) := rfl

lemma extraVertex_face (n : ℕ) (k : Fin (n + 1)) (s : OrdinalChains.{u} n) :
    extraVertex n k (s.map (faceVertices n k.succ)) = s := by
  change chainUnionMap _ _ = _
  erw [chainUnionMap_map]
  have h : (fun a => extraVertexFace n k (faceVertices n k.succ a)) = singletonChain := by
    funext a
    exact extraVertexFace_gap n k a
  rw [h]
  exact chainUnionMap_singleton s

noncomputable def extraVertexMap (n : ℕ) (k : Fin (n + 1)) :
    SimplexCategory.sd.obj ⦋n + 1⦌ ⟶ SimplexCategory.sd.obj ⦋n⦌ :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom (extraVertex n k))

lemma extraVertexMap_face (n : ℕ) (k : Fin (n + 1)) :
    SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ extraVertexMap.{u} n k = 𝟙 _ := by
  have h : PartOrd.nonemptyFiniteChainsFunctor.map
      (SimplexCategory.toPartOrd.map (SimplexCategory.δ k.succ)) ≫
      PartOrd.ofHom (extraVertex.{u} n k) = 𝟙 _ := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext s
    exact extraVertex_face n k s
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ = _
  exact (PartOrd.nerveFunctor.map_comp _ _).symm.trans
    ((congrArg PartOrd.nerveFunctor.map h).trans (PartOrd.nerveFunctor.map_id _))

noncomputable def exPairSimplex (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : (SSet.ex.obj X).obj (op ⦋n + 1⦌) :=
  ULift.up (extraVertexMap n k ≫ x.down)

lemma exPairSimplex_face (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    (SSet.ex.obj X).δ k.succ (exPairSimplex X n k x) = x := by
  apply ULift.ext
  change SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ (extraVertexMap n k ≫ x.down) = _
  erw [← Category.assoc, extraVertexMap_face, Category.id_comp]

end Thomason.Subdivision

end

end OAI
