import OAI.CategoryTheory.Globular.SmallFree

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace FiniteCoGlobularObject
variable {K : Type u} [Category.{v} K] [HasTerminal K] {q : ℕ}

noncomputable def cell (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] (S : GlobularPresheaf.{max v w})
    (k : ℕ) (hk : k ≤ q) (x : S.underlying.Cell k) : B.obj k hk ⟶ B.realization.obj S :=
  (B.globeIso k hk).inv ≫ B.realization.map (uliftYonedaEquiv.symm x)

@[reassoc] theorem cell_face (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] (S : GlobularPresheaf.{max v w})
    {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) (x : S.underlying.Cell k) :
    B.face h hk ε ≫ B.cell S k hk x =
      B.cell S j (h.le.trans hk) (S.map (Globe.face h ε).op x) := by
  have e := B.globeIso_face h hk ε
  have e' : B.face h hk ε ≫ (B.globeIso k hk).inv =
      (B.globeIso j (h.le.trans hk)).inv ≫ B.realization.map (GlobularPresheaf.face h ε) := by
    rw [← Iso.inv_hom_id_assoc (B.globeIso j (h.le.trans hk)) (B.face h hk ε), ← e]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold cell
  erw [← Category.assoc, e', Category.assoc, ← Functor.map_comp]
  congr 2
  exact (uliftYonedaEquiv_symm_map (Globe.face h ε).op x).symm

instance preservesColimits_realization (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] : PreservesColimits B.realization := by
  unfold realization
  infer_instance

end FiniteCoGlobularObject
namespace Shape

noncomputable def linearLow (n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ)
    (hk : k < n) (x : S.underlying.Cell k) : GlobularPresheaf.disk k ⟶ (linearization n).obj S :=
  realization.map (eqToHom (linearBlock_low n k hk).symm) ≫
    (linearGlobularDiagram n).cell S k (by omega) x

noncomputable def linearEdge (n : ℕ) (S : GlobularPresheaf.{0})
    (x : S.underlying.Cell n) : GlobularPresheaf.disk (n+1) ⟶ (linearization n).obj S :=
  realization.map (eqToHom (linearBlock_center n n rfl).symm) ≫
    (linearGlobularDiagram n).cell S n (by omega) x

noncomputable def linearTriple (n : ℕ) (S : GlobularPresheaf.{0})
    (x : S.underlying.Cell (n+1)) : (GlobularTheory.tripleShape n).realize ⟶ (linearization n).obj S :=
  realization.map (eqToHom (linearBlock_high n (n+1) (by omega)).symm) ≫
    (linearGlobularDiagram n).cell S (n+1) le_rfl x

@[reassoc] theorem linearLow_face (n : ℕ) (S : GlobularPresheaf.{0})
    {j k : ℕ} (h : j < k) (hk : k < n) (ε : Bool) (x : S.underlying.Cell k) :
    GlobularPresheaf.face h ε ≫ linearLow n S k hk x =
      linearLow n S j (by omega) (S.map (Globe.face h ε).op x) := by
  have e := (linearGlobularDiagram n).cell_face S h (by omega) ε x
  rw [linear_face_low n j k h hk ε] at e
  have e' := congrArg (realization.map (eqToHom (linearBlock_low n j (by omega)).symm) ≫ ·) e
  change _ = linearLow n S j (h.trans hk) _ at e'
  erw [← Category.assoc, ← Functor.map_comp] at e'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at e'
  erw [Functor.map_comp, Category.assoc] at e'
  exact e'

@[reassoc] theorem linearEdge_face (n : ℕ) (S : GlobularPresheaf.{0})
    {j : ℕ} (h : j < n) (ε : Bool) (x : S.underlying.Cell n) :
    GlobularPresheaf.face (by omega : j < n+1) ε ≫ linearEdge n S x =
      linearLow n S j h (S.map (Globe.face h ε).op x) := by
  have e := (linearGlobularDiagram n).cell_face S h (by omega) ε x
  rw [linear_face_center n j h ε] at e
  have e' := congrArg (realization.map (eqToHom (linearBlock_low n j h).symm) ≫ ·) e
  change _ = linearLow n S j h _ at e'
  erw [← Category.assoc, ← Functor.map_comp] at e'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at e'
  erw [Functor.map_comp, Category.assoc] at e'
  exact e'

@[reassoc] theorem linearTriple_face (n : ℕ) (S : GlobularPresheaf.{0})
    (ε : Bool) (x : S.underlying.Cell (n+1)) :
    realization.map (if ε then GlobularTheory.tripleLast n else GlobularTheory.tripleFirst n) ≫
      linearTriple n S x =
      linearEdge n S (S.map (Globe.face (Nat.lt_succ_self n) ε).op x) := by
  have e := (linearGlobularDiagram n).cell_face S (Nat.lt_succ_self n) le_rfl ε x
  rw [linear_face_top n ε] at e
  have e' := congrArg (realization.map (eqToHom (linearBlock_center n n rfl).symm) ≫ ·) e
  change _ = linearEdge n S _ at e'
  erw [← Category.assoc, ← Functor.map_comp] at e'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at e'
  erw [Functor.map_comp, Category.assoc] at e'
  exact e'

end Shape
namespace GlobularTheory.Model

noncomputable def smallFreeCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} (k : ℕ) (f : GlobularPresheaf.disk k ⟶ S) :
    ((smallFree hC q).obj S).obj.underlying.Cell k :=
  smallFreeGen hC q S k (f.app (op (Globe.mk k)) (ULift.up (𝟙 (Globe.mk k))))

@[simp] theorem smallFreeCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} (k : ℕ) (f : GlobularPresheaf.disk (k+1) ⟶ S) :
    ((smallFree hC q).obj S).obj.underlying.source k (smallFreeCell hC q (k+1) f) =
      smallFreeCell hC q k (GlobularPresheaf.face (Nat.lt_succ_self k) false ≫ f) := by
  unfold smallFreeCell
  erw [smallFreeGen_source]
  exact congrArg (smallFreeGen hC q S k)
    ((GlobularPresheaf.underlyingMap f).source_app k (ULift.up (𝟙 (Globe.mk (k+1))))).symm

@[simp] theorem smallFreeCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} (k : ℕ) (f : GlobularPresheaf.disk (k+1) ⟶ S) :
    ((smallFree hC q).obj S).obj.underlying.target k (smallFreeCell hC q (k+1) f) =
      smallFreeCell hC q k (GlobularPresheaf.face (Nat.lt_succ_self k) true ≫ f) := by
  unfold smallFreeCell
  erw [smallFreeGen_target]
  exact congrArg (smallFreeGen hC q S k)
    ((GlobularPresheaf.underlyingMap f).target_app k (ULift.up (𝟙 (Globe.mk (k+1))))).symm

@[simp] theorem smallFreeCell_map {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ)
    (a : GlobularPresheaf.disk k ⟶ S) :
    (underlyingMap ((smallFree hC q).map f).hom).app k (smallFreeCell hC q k a) =
      smallFreeCell hC q k (a ≫ f) :=
  smallFreeGen_map hC q f k _

@[simp] theorem smallShapeDesc_cell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨S⟩ : C.Obj))) (k : ℕ) (f : Shape.globe k ⟶ S) :
    (underlyingMap (smallShapeDesc hC q S t).hom).app k
      (smallFreeCell hC q k (Shape.realization.map f)) = Y.obj.eval (C.base f) t := by
  unfold smallFreeCell
  erw [smallShapeDesc_gen]
  have e : S.cellArrow (op (Globe.mk k)) (f.app (op (Globe.mk k))
      (ULift.up (𝟙 (Globe.mk k)))) = f := uliftYonedaEquiv.symm_apply_apply f
  erw [e]

end GlobularTheory.Model

namespace GlobularPresheaf

noncomputable def finiteRealizationDesc {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    {q : ℕ} (B : FiniteCoGlobularObject GlobularPresheaf.{0} q)
    (S : GlobularPresheaf.{0}) (hS : ∀ k, q < k → IsEmpty (S.underlying.Cell k)) (Y : K)
    (d : ∀ k (hk : k ≤ q), S.underlying.Cell k → (F.obj (B.obj k hk) ⟶ Y))
    (hd : ∀ {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) x,
      F.map (B.face h hk ε) ≫ d k hk x = d j (h.le.trans hk) (S.map (Globe.face h ε).op x)) :
    F.obj (B.realization.obj S) ⟶ Y := by
  let D (k : Globe) (x : S.obj (op k)) : (B.realization ⋙ F).obj (uliftYoneda.obj k) ⟶ Y :=
    if h : k.dim ≤ q then F.map (B.globeIso k.dim h).hom ≫ d k.dim h x
    else (hS k.dim (by omega)).false x |>.elim
  apply densityDesc (B.realization ⋙ F) S Y D
  intro k l f x
  rcases k with ⟨k⟩
  rcases l with ⟨l⟩
  have hl : l ≤ q := by
    by_contra hn
    exact (hS l (by omega)).false x
  change Globe.Face k l at f
  cases f with
  | id =>
    change (B.realization ⋙ F).map (uliftYoneda.map (𝟙 (Globe.mk k))) ≫ D _ x = _
    change _ = D _ (S.map (𝟙 (op (Globe.mk k))) x)
    erw [uliftYoneda.map_id, (B.realization ⋙ F).map_id, Category.id_comp, S.map_id]
    rfl
  | face h ε =>
    have hk := h.le.trans hl
    dsimp only [D]
    rw [dite_eq_left hl, dite_eq_left hk]
    change F.map (B.realization.map (GlobularPresheaf.face h ε)) ≫
      F.map (B.globeIso l hl).hom ≫ d l hl x = _
    erw [← Category.assoc, ← F.map_comp, B.globeIso_face, F.map_comp, Category.assoc, hd]
    rfl

@[reassoc] theorem finiteRealizationDesc_cell {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    {q : ℕ} (B : FiniteCoGlobularObject GlobularPresheaf.{0} q)
    (S : GlobularPresheaf.{0}) (hS : ∀ k, q < k → IsEmpty (S.underlying.Cell k)) (Y : K)
    (d) (hd) (k : ℕ) (hk : k ≤ q) (x : S.underlying.Cell k) :
    F.map (B.cell S k hk x) ≫ finiteRealizationDesc F B S hS Y d hd = d k hk x := by
  unfold finiteRealizationDesc FiniteCoGlobularObject.cell
  rw [F.map_comp, Category.assoc]
  dsimp only
  erw [densityDesc_cell (B.realization ⋙ F)]
  dsimp only
  erw [dite_eq_left hk, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

end GlobularPresheaf

namespace FiniteCoGlobularObject

theorem face_natural {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) {q : ℕ}
    (B : FiniteCoGlobularObject GlobularPresheaf.{0} q)
    (S : GlobularPresheaf.{0}) (Y : K)
    (d : ∀ k (hk : k ≤ q), S.underlying.Cell k → (F.obj (B.obj k hk) ⟶ Y))
    (hd : ∀ k (hk : k+1 ≤ q) (ε : Bool) x,
      F.map (if ε then B.target k hk else B.source k hk) ≫ d (k+1) hk x =
        d k (by omega) (S.map (Globe.face (Nat.lt_succ_self k) ε).op x)) :
    ∀ {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) x,
      F.map (B.face h hk ε) ≫ d k hk x =
        d j (h.le.trans hk) (S.map (Globe.face h ε).op x) := by
  intro j k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro h hk ε x
    by_cases e : j = k
    · subst j
      rw [B.face_succ]
      exact hd k hk ε x
    · have hj : j < k := by omega
      erw [← B.face_adjacent hj hk ε false, F.map_comp, Category.assoc, hd, ih hj]
      congr 1
      have e := S.map_comp (Globe.face (Nat.lt_succ_self k) false).op (Globe.face hj ε).op
      exact (ConcreteCategory.congr_hom e x).symm

end FiniteCoGlobularObject

end Grothendieck

end OAI
