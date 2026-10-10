import Mathlib
import OAI.CategoryTheory.Thomason.FiberComparisons

namespace OAI

/-! Simplex Colimits. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory CategoryTheory.Limits Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

abbrev SimplexIndex (P : Type u) [PartialOrder P] :=
  CostructuredArrow uliftYoneda.{u,0,0} (nerve P)

abbrev SimplexVertices {P : Type u} [PartialOrder P] (s : SimplexIndex P) :=
  ULift.{u} (Fin (s.left.len + 1))

noncomputable def simplexVertexOrder {P : Type u} [PartialOrder P]
    (s : SimplexIndex P) : SimplexVertices s →o P :=
  (posetSimplexOrder (uliftYonedaEquiv s.hom)).comp (orderULiftDown _)

def simplexVertexMap {P : Type u} [PartialOrder P] {s t : SimplexIndex P}
    (a : s ⟶ t) : SimplexVertices s →o SimplexVertices t :=
  (orderULiftUp _).comp (a.left.toOrderHom.comp (orderULiftDown _))

lemma simplexVertexOrder_natural {P : Type u} [PartialOrder P]
    {s t : SimplexIndex P} (a : s ⟶ t) :
    (simplexVertexOrder t).comp (simplexVertexMap a) = simplexVertexOrder s := by
  ext i
  have h := congrArg (fun f : uliftYoneda.obj s.left ⟶ nerve P => (uliftYonedaEquiv f).obj i.down) (CostructuredArrow.w a)
  have hn := uliftYonedaEquiv_naturality t.hom a.left.op
  simp only [Quiver.Hom.unop_op] at hn
  exact (congrArg (fun v : (nerve P).obj (op s.left) => v.obj i.down) hn).trans h

def liftedSimplexOrder {m n : SimplexCategory} (a : m ⟶ n) :
    ULift.{u} (Fin (m.len+1)) →o ULift.{u} (Fin (n.len+1)) :=
  (orderULiftUp _).comp (a.toOrderHom.comp (orderULiftDown _))

lemma isoNerve_natural {m n : SimplexCategory} (a : m ⟶ n) :
    uliftYoneda.{u}.map a ≫ (SSet.stdSimplex.isoNerve n.len).hom =
      (SSet.stdSimplex.isoNerve m.len).hom ≫
        nerveMap (liftedSimplexOrder a).monotone.functor := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  rfl

noncomputable def simplexCategorificationIso (m : SimplexCategory) :
    raisedOrientals.{u}.obj m ≅ categorification.obj (nerve (ULift.{u} (Fin (m.len+1)))) :=
  (categorificationSimplexIso m).symm ≪≫
    categorification.mapIso (SSet.stdSimplex.isoNerve m.len)

lemma simplexCategorificationIso_natural {m n : SimplexCategory} (a : m ⟶ n) :
    raisedOrientals.{u}.map a ≫ (simplexCategorificationIso n).hom =
      (simplexCategorificationIso m).hom ≫
        categorification.map (nerveMap (liftedSimplexOrder a).monotone.functor) := by
  change raisedOrientals.map a ≫
      (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
        raisedOrientals).app n ≫ categorification.map (SSet.stdSimplex.isoNerve n.len).hom) =
    (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
        raisedOrientals).app m ≫ categorification.map (SSet.stdSimplex.isoNerve m.len).hom) ≫ _
  erw [← Category.assoc, ((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals).naturality a]
  change ((_ : raisedOrientals.obj m ⟶ categorification.obj (uliftYoneda.obj m)) ≫
    categorification.map (uliftYoneda.map a)) ≫
      categorification.map (SSet.stdSimplex.isoNerve n.len).hom = _
  erw [Category.assoc, ← categorification.map_comp, isoNerve_natural, categorification.map_comp,
    Category.assoc]
  rfl

lemma simplexVertexOrder_nerve {P : Type u} [PartialOrder P] (s : SimplexIndex P) :
    (SSet.stdSimplex.isoNerve s.left.len).hom ≫
      nerveMap (simplexVertexOrder s).monotone.functor = s.hom := by
  apply uliftYonedaEquiv.injective
  apply nerve.ext_of_isThin
  rfl

noncomputable def posetSimplexDiagram (P : Type u) [PartialOrder P] :
    SimplexIndex P ⥤ OmegaCategory.{u} where
  obj s := categorification.obj (nerve (SimplexVertices s))
  map a := categorification.map (nerveMap (simplexVertexMap a).monotone.functor)
  map_id s := by
    have h : nerveMap (simplexVertexMap (𝟙 s)).monotone.functor = 𝟙 (nerve (SimplexVertices s)) := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro t
      apply nerve.ext_of_isThin
      rfl
    rw [h, categorification.map_id]
  map_comp a b := by
    rw [← categorification.map_comp]
    congr 1

noncomputable def posetSimplexDiagramIso (P : Type u) [PartialOrder P] :
    categorificationSimplexDiagram (nerve P) ≅ posetSimplexDiagram P :=
  NatIso.ofComponents (fun s => simplexCategorificationIso s.left)
    (fun a => simplexCategorificationIso_natural a.left)

noncomputable def posetSimplexCocone (P : Type u) [PartialOrder P] :
    Cocone (posetSimplexDiagram P) where
  pt := categorification.obj (nerve P)
  ι.app s := categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)
  ι.naturality s t a := by
    change categorification.map (nerveMap (simplexVertexMap a).monotone.functor) ≫
      categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫ 𝟙 _
    rw [Category.comp_id, ← categorification.map_comp]
    congr 1
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro k
    apply nerve.ext_of_isThin
    funext i
    exact congrArg (fun h : SimplexVertices s →o P => h (ULift.up (k.obj i).down))
      (simplexVertexOrder_natural a)

lemma posetSimplexCocone_leg {P : Type u} [PartialOrder P] (s : SimplexIndex P) :
    (simplexCategorificationIso s.left).hom ≫ (posetSimplexCocone P).ι.app s =
      (categorificationSimplexCocone (nerve P)).ι.app s := by
  change (_ ≫ categorification.map (SSet.stdSimplex.isoNerve s.left.len).hom) ≫
    categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) = _
  rw [Category.assoc, ← categorification.map_comp, simplexVertexOrder_nerve]
  rfl

noncomputable def posetSimplexIsColimit (P : Type u) [PartialOrder P] :
    IsColimit (posetSimplexCocone P) := by
  apply (IsColimit.precomposeHomEquiv (posetSimplexDiagramIso P) _).toFun
  exact IsColimit.ofIsoColimit (categorificationSimplexIsColimit (nerve P))
    (Cocone.ext (Iso.refl _) (fun s => by
      change (categorificationSimplexCocone (nerve P)).ι.app s ≫ 𝟙 _ =
        (simplexCategorificationIso s.left).hom ≫ (posetSimplexCocone P).ι.app s
      rw [Category.comp_id]
      exact (posetSimplexCocone_leg s).symm))

noncomputable def posetSimplexOverDiagram {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) : SimplexIndex P ⥤ Over interval.{u} where
  obj s := Over.mk (posetCategorificationLabel (f.comp (simplexVertexOrder s)))
  map {s t} a := Over.homMk ((posetSimplexDiagram P).map a) (by
    change categorification.map (nerveMap (simplexVertexMap a).monotone.functor) ≫
      posetCategorificationLabel (f.comp (simplexVertexOrder t)) =
        posetCategorificationLabel (f.comp (simplexVertexOrder s))
    rw [posetCategorificationLabel_natural]
    apply congrArg posetCategorificationLabel
    exact congrArg f.comp (simplexVertexOrder_natural a))
  map_id s := by
    apply Over.OverMorphism.ext
    exact (posetSimplexDiagram P).map_id s
  map_comp a b := by
    apply Over.OverMorphism.ext
    exact (posetSimplexDiagram P).map_comp a b

noncomputable def posetSimplexOverCocone {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) : Cocone (posetSimplexOverDiagram f) where
  pt := Over.mk (posetCategorificationLabel f)
  ι.app s := posetCategorificationOverMap (simplexVertexOrder s) f
  ι.naturality s t a := by
    apply Over.OverMorphism.ext
    exact (posetSimplexCocone P).ι.naturality a

noncomputable def posetSimplexOverIsColimit {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) : IsColimit (posetSimplexOverCocone f) :=
  isColimitOfReflects (Over.forget interval) (posetSimplexIsColimit P)

noncomputable def posetSimplexFiberIsColimit {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    IsColimit ((fiberFunctor (intervalVertex e)).mapCocone (posetSimplexOverCocone f)) := by
  have : PreservesColimitsOfSize.{0,u} (fiberFunctor.{u} (intervalVertex e)) := by
    by_cases he : e = 0
    · subst e; infer_instance
    · have he1 : e = 1 := by omega
      subst e; infer_instance
  exact isColimitOfPreserves (fiberFunctor (intervalVertex e)) (posetSimplexOverIsColimit f)

lemma finiteFiberAssembly_natural
    {L M P : Type u} [LinearOrder L] [Finite L] [LinearOrder M] [Finite M]
    [PartialOrder P] (f : P →o Fin 2) (e : Fin 2)
    (σ : L →o P) (τ : M →o P) (g : L →o M) (h : τ.comp g = σ)
    (a : Over.mk (posetCategorificationLabel (f.comp σ)) ⟶
      Over.mk (posetCategorificationLabel (f.comp τ)))
    (ha : a.left = categorification.map (nerveMap g.monotone.functor)) :
    (fiberFunctor (intervalVertex e)).map a ≫
      ((posetCategorificationFiberIsoFinite M (f.comp τ) e).inv ≫
        categorification.map (nerveMap (posetLevelMap τ f e).monotone.functor)) =
    (posetCategorificationFiberIsoFinite L (f.comp σ) e).inv ≫
      categorification.map (nerveMap (posetLevelMap σ f e).monotone.functor) := by
  subst σ
  have he : a = posetCategorificationOverMap g (f.comp τ) := by
    apply Over.OverMorphism.ext
    exact ha
  rw [he]
  let sourceInverse := (posetCategorificationFiberIsoFinite L ((f.comp τ).comp g) e).inv
  let targetInverse := (posetCategorificationFiberIsoFinite M (f.comp τ) e).inv
  let fiberMap : ((posetCategorificationLabel ((f.comp τ).comp g)).fiber
      (intervalVertex e)).category ⟶
      ((posetCategorificationLabel (f.comp τ)).fiber (intervalVertex e)).category :=
    (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g (f.comp τ))
  let firstMap := categorification.map
    (nerveMap (posetLevelMap g (f.comp τ) e).monotone.functor)
  let secondMap := categorification.map
    (nerveMap (posetLevelMap τ f e).monotone.functor)
  have naturality : fiberMap ≫ targetInverse = sourceInverse ≫ firstMap :=
    posetCategorificationFiberMap_inverse_natural g (f.comp τ) e
  change fiberMap ≫ (targetInverse ≫ secondMap) = sourceInverse ≫
    categorification.map (nerveMap (posetLevelMap (τ.comp g) f e).monotone.functor)
  calc
    _ = (fiberMap ≫ targetInverse) ≫ secondMap :=
      (Category.assoc _ _ _).symm
    _ = (sourceInverse ≫ firstMap) ≫ secondMap :=
      congrArg (fun morphism => morphism ≫ secondMap) naturality
    _ = sourceInverse ≫ (firstMap ≫ secondMap) := Category.assoc _ _ _
    _ = sourceInverse ≫
        categorification.map (nerveMap (posetLevelMap g (f.comp τ) e).monotone.functor ≫
          nerveMap (posetLevelMap τ f e).monotone.functor) :=
      congrArg (fun morphism => sourceInverse ≫ morphism)
        (categorification.map_comp _ _).symm
    _ = _ := rfl

noncomputable def posetFiberInverseCocone {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    Cocone (posetSimplexOverDiagram f ⋙ fiberFunctor (intervalVertex e)) where
  pt := categorification.obj (nerve {a // f a = e})
  ι.app s := (posetCategorificationFiberIsoFinite (SimplexVertices s)
      (f.comp (simplexVertexOrder s)) e).inv ≫
    categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor)
  ι.naturality s t a := by
    change (fiberFunctor (intervalVertex e)).map ((posetSimplexOverDiagram f).map a) ≫ _ =
      _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact finiteFiberAssembly_natural f e _ _ _ (simplexVertexOrder_natural a) _ rfl

noncomputable def posetCategorificationFiberInverse {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    ((posetCategorificationLabel f).fiber (intervalVertex e)).category ⟶
      categorification.obj (nerve {a // f a = e}) :=
  (posetSimplexFiberIsColimit f e).desc (posetFiberInverseCocone f e)

lemma posetCategorificationFiberInverse_fac {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) (s : SimplexIndex P) :
    (fiberFunctor (intervalVertex e)).map
        (posetCategorificationOverMap (simplexVertexOrder s) f) ≫
      posetCategorificationFiberInverse f e =
    (posetCategorificationFiberIsoFinite (SimplexVertices s)
      (f.comp (simplexVertexOrder s)) e).inv ≫
      categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor) :=
  (posetSimplexFiberIsColimit f e).fac (posetFiberInverseCocone f e) s

lemma posetCategorificationFiberInverse_map {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberInverse f e ≫ posetCategorificationFiberMap f e = 𝟙 _ := by
  apply (posetSimplexFiberIsColimit f e).hom_ext
  intro s
  change (fiberFunctor (intervalVertex e)).map
    (posetCategorificationOverMap (simplexVertexOrder s) f) ≫
      (posetCategorificationFiberInverse f e ≫ posetCategorificationFiberMap f e) = _
  erw [← Category.assoc, posetCategorificationFiberInverse_fac, Category.assoc,
    posetCategorificationFiberMap_natural]
  change (posetCategorificationFiberIsoFinite (SimplexVertices s)
    (f.comp (simplexVertexOrder s)) e).inv ≫
      ((posetCategorificationFiberIsoFinite (SimplexVertices s)
        (f.comp (simplexVertexOrder s)) e).hom ≫ _) = _
  erw [Iso.inv_hom_id_assoc]
  exact (Category.comp_id _).symm

noncomputable def simplexIndexMap {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (g : P →o Q) (s : SimplexIndex P) : SimplexIndex Q :=
  CostructuredArrow.mk (s.hom ≫ nerveMap g.monotone.functor)

lemma posetCategorificationFiberMap_inverse {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberMap f e ≫ posetCategorificationFiberInverse f e = 𝟙 _ := by
  apply (posetSimplexIsColimit {a // f a = e}).hom_ext
  intro t
  let s : SimplexIndex P := simplexIndexMap (posetLevelInclusion f e) t
  let k : SimplexVertices t →o {i : SimplexVertices s // (f.comp (simplexVertexOrder s)) i = e} :=
    ⟨fun i => ⟨i, (simplexVertexOrder t i).property⟩, fun _ _ h => h⟩
  have hτ : categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) =
      categorification.map (nerveMap k.monotone.functor) ≫
        categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor) := by
    rw [← categorification.map_comp]
    congr 1
  change categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) ≫
    (posetCategorificationFiberMap f e ≫ posetCategorificationFiberInverse f e) =
      categorification.map (nerveMap (simplexVertexOrder t).monotone.functor) ≫ 𝟙 _
  calc
    _ = (categorification.map (nerveMap k.monotone.functor) ≫
        categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor)) ≫
      (posetCategorificationFiberMap f e ≫ posetCategorificationFiberInverse f e) := by rw [hτ]
    _ = categorification.map (nerveMap k.monotone.functor) ≫
      (posetCategorificationFiberMap (f.comp (simplexVertexOrder s)) e ≫
        ((fiberFunctor (intervalVertex e)).map
          (posetCategorificationOverMap (simplexVertexOrder s) f) ≫
            posetCategorificationFiberInverse f e)) := by
      erw [Category.assoc, ← Category.assoc _ (posetCategorificationFiberMap f e),
        posetCategorificationFiberMap_natural, Category.assoc]
    _ = categorification.map (nerveMap k.monotone.functor) ≫
      (posetCategorificationFiberMap (f.comp (simplexVertexOrder s)) e ≫
        ((posetCategorificationFiberIsoFinite (SimplexVertices s)
          (f.comp (simplexVertexOrder s)) e).inv ≫
            categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor))) := by
      erw [posetCategorificationFiberInverse_fac]
    _ = categorification.map (nerveMap k.monotone.functor) ≫
        categorification.map (nerveMap (posetLevelMap (simplexVertexOrder s) f e).monotone.functor) := by
      change _ ≫ ((posetCategorificationFiberIsoFinite (SimplexVertices s)
        (f.comp (simplexVertexOrder s)) e).hom ≫ _) = _
      rw [Iso.hom_inv_id_assoc]
    _ = _ := by rw [← hτ, Category.comp_id]

noncomputable def posetCategorificationFiberIso {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) :
    categorification.obj (nerve {a // f a = e}) ≅
      ((posetCategorificationLabel f).fiber (intervalVertex e)).category where
  hom := posetCategorificationFiberMap f e
  inv := posetCategorificationFiberInverse f e
  hom_inv_id := posetCategorificationFiberMap_inverse f e
  inv_hom_id := posetCategorificationFiberInverse_map f e

theorem posetCategorificationFiberMap_isIso {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) (e : Fin 2) : IsIso (posetCategorificationFiberMap f e) :=
  (posetCategorificationFiberIso f e).isIso_hom

theorem posetCategorificationFiniteFiberMap_isIso (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (f : P →o Fin 2) (e : Fin 2) :
    IsIso (posetCategorificationFiniteFiberMap n hn f e) := by
  have := posetCategorificationFiberMap_isIso f e
  unfold posetCategorificationFiniteFiberMap
  exact IsIso.comp_isIso'
    (CategoryTheory.Functor.map_isIso _ _)
    ((truncationFiberIso n hn e).app (Over.mk (posetCategorificationLabel f))).isIso_inv

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex DirectedComplex.Table
variable {E : Type u} [PartialOrder E]

lemma supportedOn_of_le_positive {S : Set E} {x y : Chains E}
    (hx : Positive x) (hxy : ∀ w, x w ≤ y w) (hy : y ∈ supportedOn S) :
    x ∈ supportedOn S := by
  rw [mem_supportedOn_iff] at hy ⊢
  intro w hw
  apply hy w
  exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hx w) (Ne.symm hw)) (hxy w))

lemma supportedOn_of_add_positive {S : Set E} {x y : Chains E}
    (hx : Positive x) (hy : Positive y) (h : x+y ∈ supportedOn S) :
    x ∈ supportedOn S ∧ y ∈ supportedOn S := by
  constructor
  · exact supportedOn_of_le_positive hx (fun w => by simpa using hy w) h
  · exact supportedOn_of_le_positive hy (fun w => by simpa using hx w) h

lemma vertex_supportedOn_iff (a : E) (S : Set E) :
    bracket [a] ∈ supportedOn S ↔ a ∈ S := by
  constructor
  · intro h
    apply (mem_supportedOn_iff S _).mp h ⟨[a], by simp⟩
      (by simp [bracket_of_pairwise]) a (by simp)
  · exact fun ha => bracket_mem_supportedOn (by simpa)

lemma edge_supportedOn_iff {a b : E} (hab : a < b) (S : Set E) :
    bracket [a,b] ∈ supportedOn S ↔ a ∈ S ∧ b ∈ S := by
  have hh : [a,b].Pairwise (· < ·) := by simpa
  constructor
  · intro h
    have := (mem_supportedOn_iff S _).mp h ⟨[a,b], hh⟩
      (by simp [bracket_of_pairwise hh])
    exact ⟨this a (by simp), this b (by simp)⟩
  · rintro ⟨ha,hb⟩
    exact bracket_mem_supportedOn (by simpa using And.intro ha hb)

lemma simplexAtom_source_zero (a : E) (l : List E)
    (h : (a :: l).Pairwise (· ≤ ·)) :
    ((simplexAtom a l h).table.row 0 false).val = bracket [a] := by
  cases l <;> rfl

lemma simplexAtom_vertices_supported {S : Set E} (a : E) (l : List E)
    (h : (a :: l).Pairwise (· < ·))
    (h0 : ((simplexAtom a l (h.imp le_of_lt)).table.row 0 false).val ∈ supportedOn S)
    (h1 : ((simplexAtom a l (h.imp le_of_lt)).table.row 1 true).val ∈ supportedOn S) :
    ∀ b ∈ a :: l, b ∈ S := by
  have ha : a ∈ S := (vertex_supportedOn_iff a S).mp (by simpa [simplexAtom_source_zero] using h0)
  induction l generalizing a with
  | nil => simpa using ha
  | cons b l ih =>
    have hb : a < b := (List.pairwise_cons.mp h).1 b (by simp)
    have he : ((simplexAtom a (b :: l) (h.imp le_of_lt)).table.row 1 true).val =
        ((simplexAtom b l (h.tail.imp le_of_lt)).table.row 1 true).val + bracket [a,b] := by
      change _ + prepend a ((simplexAtom b l (h.tail.imp le_of_lt)).table.row 0 false).val = _
      erw [simplexAtom_source_zero, prepend_bracket]
    rw [he] at h1
    obtain ⟨ht,he⟩ := supportedOn_of_add_positive
      ((simplexAtom b l (h.tail.imp le_of_lt)).table.positive 1 true)
      (bracket_positive [a,b]) h1
    have hbs : b ∈ S := ((edge_supportedOn_iff hb S).mp he).2
    have htail := ih b h.tail
      (by rw [simplexAtom_source_zero]; exact (vertex_supportedOn_iff b S).mpr hbs) ht hbs
    simpa using List.forall_mem_cons.mpr ⟨ha, htail⟩

lemma table_finish_supported {S : Set E} (x : Table (complex E))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    (x.row 0 true).val ∈ supportedOn S := by
  have he := congrArg Subtype.val (x.boundary 0 true)
  change boundary (x.row 1 true).val = (x.row 0 true).val - (x.row 0 false).val at he
  rw [eq_sub_iff_add_eq] at he
  rw [← he]
  exact (supportedOn S).add_mem (boundary_mem_supportedOn h1) h0

lemma oriental_support_of_target {N : ℕ} (S : Set (Fin (N+1))) (x : Table (complex (Fin (N+1))))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  have hx := oriental_all_atomic x
  induction hx with
  | atom a l h =>
    intro p b
    exact supportedOn_mono (simplexAtom_vertices_supported a l h h0 h1)
      ((simplexAtom a l (h.imp le_of_lt)).supported p b)
  | compose k x y h hx hy ihx ihy =>
    have h0x : (x.row 0 false).val ∈ supportedOn S := by
      cases k with
      | zero => exact h0
      | succ k => simpa only [comp_row, Nat.zero_lt_succ, ite_true] using h0
    have h1y : (y.row 1 true).val ∈ supportedOn S := by
      cases k with
      | zero =>
        have hh : (x.row 1 true).val + (y.row 1 true).val ∈ supportedOn S := by
          exact h1
        exact (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true) hh).2
      | succ k =>
        cases k with
        | zero => simpa using h1
        | succ k =>
          have he := lower_rows_eq h (show 1 < k+1+1 by omega) true
          simpa [show 1 < k+1+1 by omega, he] using h1
    have hxy : ∀ p b, (x.row p b).val ∈ supportedOn S ∧ (y.row p b).val ∈ supportedOn S := by
      cases k with
      | zero =>
        have h1x : (x.row 1 true).val ∈ supportedOn S :=
          (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true)
            h1).1
        have h0y : (y.row 0 false).val ∈ supportedOn S := by
          rw [← matching_row_eq h]
          exact table_finish_supported x h0x h1x
        exact fun p b => ⟨ihx h0x h1x p b, ihy h0y h1y p b⟩
      | succ k =>
        have h0y : (y.row 0 false).val ∈ supportedOn S := by
          rw [← lower_rows_eq h (Nat.zero_lt_succ k) false]
          exact h0x
        have hy' := ihy h0y h1y
        have h1x : (x.row 1 true).val ∈ supportedOn S := by
          cases k with
          | zero => rw [matching_row_eq h]; exact hy' 1 false
          | succ k =>
            rw [lower_rows_eq h (show 1 < k+1+1 by omega) true]
            exact h1y
        exact fun p b => ⟨ihx h0x h1x p b, hy' p b⟩
    intro p b
    simp only [Table.comp_row]
    split_ifs
    · exact (hxy p b).1
    · exact (hxy p true).2
    · exact (hxy p false).1
    · exact (supportedOn S).add_mem (hxy p b).1 (hxy p b).2

lemma table_support_of_target_finite [Finite E] (S : Set E) (x : Table (complex E))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  classical
  let : Nonempty E := ⟨(table_zero_row_vertex x false).choose⟩
  let : Fintype E := Fintype.ofFinite E
  let : Fintype (LinearExtension E) := inferInstanceAs (Fintype E)
  let : Nonempty (LinearExtension E) := inferInstanceAs (Nonempty E)
  let n := Fintype.card (LinearExtension E) - 1
  have hn : Fintype.card (LinearExtension E) = n+1 := by
    have := Fintype.card_pos (α := LinearExtension E)
    dsimp only [n]
    omega
  let e : Fin (n+1) ≃o LinearExtension E := Fintype.orderIsoFinOfCardEq (LinearExtension E) hn
  let f : E →o Fin (n+1) := e.symm.toOrderEmbedding.toOrderHom.comp toLinearExtension
  have hf : Function.Injective f := e.symm.injective.comp (fun _ _ h => h)
  have hS : f ⁻¹' (f '' S) = S := Set.preimage_image_eq _ hf
  have hm : ∀ p b, map f (x.row p b).val ∈ supportedOn (f '' S) :=
    oriental_support_of_target (f '' S) ((complexMap f).table x)
      (map_supportedOn f (S := S) (T := f '' S) (fun a ha => ⟨a,ha,rfl⟩) h0)
      (map_supportedOn f (S := S) (T := f '' S) (fun a ha => ⟨a,ha,rfl⟩) h1)
  intro p b
  rw [← hS]
  exact supportedOn_of_injective_map f hf (hm p b)

lemma table_finite_support (x : Table (complex E)) :
    ∃ S : Finset E, ∀ p b, (x.row p b).val ∈ supportedOn (S : Set E) := by
  classical
  obtain ⟨n, hn⟩ := x.bounded
  let S := (Finset.range (n+1)).biUnion fun p => (Finset.univ : Finset Bool).biUnion fun b =>
    (x.row p b).val.support.biUnion fun w => w.val.toFinset
  refine ⟨S, ?_⟩
  intro p b
  rw [mem_supportedOn_iff]
  intro w hw a ha
  have hp : p < n+1 := by
    by_contra h
    have hnp : n < p := by omega
    have hz := congrArg Subtype.val (hn p hnp b)
    change (x.row p b).val = 0 at hz
    rw [hz] at hw
    exact hw rfl
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_range.mpr hp,
    Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b,
      Finset.mem_biUnion.mpr ⟨w, Finsupp.mem_support_iff.mpr hw, List.mem_toFinset.mpr ha⟩⟩⟩

lemma table_support_of_target (S : Set E) (x : Table (complex E))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  classical
  obtain ⟨T, hT⟩ := table_finite_support x
  let : Finite (Subtype (T : Set E)) := T.finite_toSet.to_subtype
  let y := restrictTable (T : Set E) x hT
  let i : ↥(T : Set E) →o E := (OrderEmbedding.subtype (T : Set E)).toOrderHom
  have hm (p : ℕ) (b : Bool) : map i (y.row p b).val = (x.row p b).val :=
    congrArg (fun z => (z.row p b).val) (table_map_restrictTable (T : Set E) x hT)
  have hy : ∀ p b, (y.row p b).val ∈ supportedOn (i ⁻¹' S) :=
    table_support_of_target_finite (E := ↥(T : Set E)) (i ⁻¹' S) y
      (supportedOn_of_injective_map i Subtype.val_injective (by rw [hm]; exact h0))
      (supportedOn_of_injective_map i Subtype.val_injective (by rw [hm]; exact h1))
  intro p b
  rw [← hm]
  exact map_supportedOn i (fun _ h => h) (hy p b)

lemma wordBoundary_pair (a b : E) : wordBoundary [a,b] = bracket [b] - bracket [a] := by
  simp [wordBoundary, prepend_bracket]

lemma positive_peel {c : Chains E} (hc : Positive c) (w : Word E) (hw : 0 < c w) :
    Positive (c - bracket w.val) := by
  classical
  rw [bracket_of_pairwise w.property]
  intro t
  change 0 ≤ c t - (Finsupp.single w 1) t
  by_cases he : w = t
  · subst t; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne (Ne.symm he), sub_zero]; exact hc t

lemma positive_unit_flow_outgoing {c : Chains E} (hg : c ∈ grade 2) (hp : Positive c)
    {s t : E} (hst : s ≠ t) (hb : boundary c = bracket [t] - bracket [s]) :
    ∃ b, ∃ h : s < b, 0 < c ⟨[s,b], by simpa using h⟩ := by
  classical
  let v : Word E := ⟨[s], by simp⟩
  have hneg : boundary c v < 0 := by
    rw [hb]
    simp [v, bracket_apply, Ne.symm hst]
  rw [boundary_apply, Finsupp.sum] at hneg
  have hex : ∃ w ∈ c.support, c w * wordBoundary w.val v < 0 := by
    by_contra! hn
    exact (not_lt_of_ge (Finset.sum_nonneg hn)) hneg
  obtain ⟨w, hw, hn⟩ := hex
  have hwpos : 0 < c w := lt_of_le_of_ne (hp w) (Ne.symm (Finsupp.mem_support_iff.mp hw))
  have hlen := (mem_grade_iff 2 c).mp hg w (Finsupp.mem_support_iff.mp hw)
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hlen
  have hlt : a < b := by simpa [hab] using w.property
  have hr : wordBoundary w.val v < 0 := by
    by_contra h
    exact (not_lt_of_ge (mul_nonneg hwpos.le (not_lt.mp h))) hn
  have has : a = s := by
    by_contra hn
    rw [hab, wordBoundary_pair] at hr
    simp [v, bracket_apply, hn] at hr
    split_ifs at hr <;> omega
  subst a
  refine ⟨b, hlt, ?_⟩
  have he : w = ⟨[s,b], by simpa using hlt⟩ := Subtype.ext hab
  simpa only [he] using hwpos

lemma positive_unit_flow_chain {c : Chains E} (hg : c ∈ grade 2) (hp : Positive c)
    (s t : E) (hb : boundary c = bracket [t] - bracket [s]) :
    ∃ S : Set E, S.Finite ∧ (∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) ∧
      s ∈ S ∧ t ∈ S ∧ (∀ a ∈ S, s ≤ a ∧ a ≤ t) ∧ c ∈ supportedOn S := by
  classical
  generalize hm : (chainMass c).toNat = m
  induction m using Nat.strong_induction_on generalizing c s t with
  | h m ih =>
    by_cases hst : s = t
    · subst t
      have hz : c = 0 := positive_cycle_zero_partial hg hp (by simpa using hb)
      refine ⟨{s}, Set.finite_singleton s, ?_, by simp, by simp, ?_, ?_⟩
      · intro a ha b hb
        simp only [Set.mem_singleton_iff] at ha hb
        subst a; subst b; exact Or.inl le_rfl
      · intro a ha
        simp only [Set.mem_singleton_iff] at ha
        subst a; exact ⟨le_rfl, le_rfl⟩
      · rw [hz]; exact (supportedOn _).zero_mem
    · obtain ⟨b, hsb, hpos⟩ := positive_unit_flow_outgoing hg hp hst hb
      let w : Word E := ⟨[s,b], by simpa using hsb⟩
      let d := c - bracket w.val
      have hdg : d ∈ grade 2 := (grade 2).sub_mem hg (bracket_mem_grade [s,b])
      have hdp : Positive d := positive_peel hp w hpos
      have hdb : boundary d = bracket [t] - bracket [b] := by
        dsimp only [d]
        rw [map_sub, hb, boundary_bracket (w.property.imp le_of_lt), wordBoundary_pair]
        abel
      have hmass : chainMass d = chainMass c - 1 := by rw [map_sub, chainMass_bracket]
      have hlt : (chainMass d).toNat < m := by
        rw [← hm, Int.toNat_lt_toNat (chainMass_pos hp hpos), hmass]
        omega
      obtain ⟨S, hSf, hSc, hbS, htS, hSbounds, hdS⟩ := ih _ hlt hdg hdp b t hdb rfl
      have hsle : ∀ a ∈ S, s ≤ a := fun a ha => hsb.le.trans (hSbounds a ha).1
      refine ⟨insert s S, hSf.insert s, ?_, Set.mem_insert s S, Set.mem_insert_of_mem s htS, ?_, ?_⟩
      · intro a ha b hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact Or.inl le_rfl
          · exact Or.inl (hsle b hb)
        · rcases hb with rfl | hb
          · exact Or.inr (hsle a ha)
          · exact hSc a ha b hb
      · intro a ha
        rcases ha with rfl | ha
        · exact ⟨le_rfl, hsle t htS⟩
        · exact ⟨hsle a ha, (hSbounds a ha).2⟩
      · have he : c = d + bracket [s,b] := by dsimp [d,w]; abel
        rw [he]
        apply (supportedOn _).add_mem
        · exact supportedOn_mono (Set.subset_insert s S) hdS
        · apply bracket_mem_supportedOn
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with ha | ha
          · subst a; exact Set.mem_insert s S
          · subst a; exact Set.mem_insert_of_mem s hbS

lemma table_finite_chain_support (x : Table (complex E)) :
    ∃ S : Set E, S.Finite ∧ (∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) ∧
      (∀ p b, (x.row p b).val ∈ supportedOn S) := by
  obtain ⟨s, hs⟩ := table_zero_row_vertex x false
  obtain ⟨t, ht⟩ := table_zero_row_vertex x true
  have hb : boundary (x.row 1 true).val = bracket [t] - bracket [s] := by
    have he := congrArg Subtype.val (x.boundary 0 true)
    change boundary (x.row 1 true).val = (x.row 0 true).val - (x.row 0 false).val at he
    simpa [hs, ht] using he
  obtain ⟨S, hSf, hSc, hsS, htS, hbounds, h1⟩ :=
    positive_unit_flow_chain (x.row 1 true).property (x.positive 1 true) s t hb
  refine ⟨S,hSf,hSc, table_support_of_target S x ?_ h1⟩
  rw [hs]
  exact (vertex_supportedOn_iff s S).mpr hsS

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex DirectedComplex.Table
variable {E : Type u} [PartialOrder E]

lemma table_truncate_supported (S : Set E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) (k : ℕ) (e : Bool) :
    ∀ p b, ((truncate k e x).row p b).val ∈ supportedOn S := by
  intro p b
  simp only [truncate_row]
  split_ifs
  · exact hx p b
  · exact hx p e
  · exact (supportedOn S).zero_mem

lemma table_comp_supported_factors (S : Set E) (k : ℕ) (x y : Table (complex E))
    (h : truncate k true x = truncate k false y)
    (hz : ∀ p b, ((comp k x y h).row p b).val ∈ supportedOn S) :
    (∀ p b, (x.row p b).val ∈ supportedOn S) ∧
      (∀ p b, (y.row p b).val ∈ supportedOn S) := by
  have h0 := hz 0 false
  have h1 := hz 1 true
  have h0x : (x.row 0 false).val ∈ supportedOn S := by
    cases k with
    | zero => exact h0
    | succ k => simpa only [comp_row, Nat.zero_lt_succ, ite_true] using h0
  have h1y : (y.row 1 true).val ∈ supportedOn S := by
    cases k with
    | zero => exact (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true) h1).2
    | succ k =>
      cases k with
      | zero => simpa using h1
      | succ k =>
        have he := lower_rows_eq h (show 1 < k+1+1 by omega) true
        simpa [show 1 < k+1+1 by omega, he] using h1
  cases k with
  | zero =>
    have h1x : (x.row 1 true).val ∈ supportedOn S :=
      (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true) h1).1
    have h0y : (y.row 0 false).val ∈ supportedOn S := by
      rw [← matching_row_eq h]
      exact table_finish_supported x h0x h1x
    exact ⟨table_support_of_target S x h0x h1x, table_support_of_target S y h0y h1y⟩
  | succ k =>
    have h0y : (y.row 0 false).val ∈ supportedOn S := by
      rw [← lower_rows_eq h (Nat.zero_lt_succ k) false]
      exact h0x
    have hy' := table_support_of_target S y h0y h1y
    have h1x : (x.row 1 true).val ∈ supportedOn S := by
      cases k with
      | zero => rw [matching_row_eq h]; exact hy' 1 false
      | succ k =>
        rw [lower_rows_eq h (show 1 < k+1+1 by omega) true]
        exact h1y
    exact ⟨table_support_of_target S x h0x h1x, hy'⟩

end Thomason.NormalizedChains

end

end OAI
