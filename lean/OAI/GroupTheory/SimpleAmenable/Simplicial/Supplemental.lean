import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleReindex
import OAI.GroupTheory.SimpleAmenable.Simplicial.StringEvaluation

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

section
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleInnerReindex_id (p q r:ℕ) :
    tripleInnerReindex W q r (OrderHom.id (α:=Fin (p+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact Diagram.map_map_reindex_id
lemma tripleInnerReindex_comp (q r:ℕ) {p s t:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (v:Fin (s+1)→oFin (t+1)) :
    tripleInnerReindex W q r (v.comp u) =
      tripleInnerReindex W q r v ≫ tripleInnerReindex W q r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact Diagram.map_map_reindex_comp u v

noncomputable def innerResolutionRows (q r:ℕ) : SimplicialObject SSet where
  obj p := SimplicialDiagonal.nerveDiagonal.obj (tripleDiagramHorizontal W p.unop.len q r)
  map f := SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q r f.unop.toOrderHom)
  map_id p := by
    change SimplicialDiagonal.nerveDiagonal.map
      (tripleInnerReindex W q r (OrderHom.id (α:=Fin (p.unop.len+1)))) = _
    rw [tripleInnerReindex_id,CategoryTheory.Functor.map_id]
  map_comp f g := by rw [show (f ≫ g).unop.toOrderHom = f.unop.toOrderHom.comp g.unop.toOrderHom from rfl,
    tripleInnerReindex_comp,Functor.map_comp]
noncomputable def innerNerveRows (q r:ℕ) : SimplicialObject SSet where
  obj p := nerve (Diagram (Diagram (Diagram C (Fin (p.unop.len+1))) (Fin (q+1))) (Fin (r+1)))
  map f := nerveMap (Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)))
  map_id p := by
    change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (Diagram.reindex (C:=C) (OrderHom.id (α:=Fin (p.unop.len+1))))))=𝟙 _
    rw [Diagram.map_map_reindex_id]
    rfl
  map_comp f g := by
    change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1))
      (Diagram.reindex (C:=C) (f.unop.toOrderHom.comp g.unop.toOrderHom)))) = _
    rw [Diagram.map_map_reindex_comp]
    rfl

noncomputable def innerResolutionAugmentation (q r:ℕ) :
    innerResolutionRows W q r ⟶ innerNerveRows (C:=C) q r where
  app p := tripleResolutionAugmentation W p.unop.len q r
  naturality _ _ f := tripleResolutionAugmentation_inner_natural W q r f.unop.toOrderHom
noncomputable instance innerResolutionTotal_isIso (q r j:ℕ) :
    IsIso (SSet.homologyMap
      (SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W q r))
      DiagonalResolution.Z j) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p n
  exact tripleResolutionAugmentation_isIso W p.unop.len q r n

lemma tripleInnerMiddle_commute (r:ℕ) {p s q t:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (v:Fin (q+1)→oFin (t+1)) :
    tripleInnerReindex W t r u ≫ tripleMiddleReindex W p r v =
      tripleMiddleReindex W s r v ≫ tripleInnerReindex W q r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact Diagram.map_map_reindex (Diagram.reindex u) v
noncomputable def innerRowsMiddle (r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    innerResolutionRows W s r ⟶ innerResolutionRows W q r where
  app p := SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p.unop.len r u)
  naturality n m f := by
    change SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W s r f.unop.toOrderHom) ≫
      SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W m.unop.len r u) = _
    rw [←Functor.map_comp,tripleInnerMiddle_commute,Functor.map_comp]
    rfl
noncomputable def innerNerveRowsMiddle (r:ℕ) {q s:ℕ} (u:Fin (q+1)→oFin (s+1)) :
    innerNerveRows (C:=C) s r ⟶ innerNerveRows (C:=C) q r where
  app p := nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram C (Fin (p.unop.len+1))) u))
  naturality n m f := by
    change nerveMap (Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)) ⋙
      Diagram.map (Diagram.reindex u)) = nerveMap (Diagram.map (Diagram.reindex u) ⋙
      Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)))
    rw [Diagram.map_map_reindex]
lemma innerResolutionAugmentation_middle_natural (r:ℕ) {q s:ℕ}
    (u:Fin (q+1)→oFin (s+1)) :
    innerRowsMiddle W r u ≫ innerResolutionAugmentation W q r =
      innerResolutionAugmentation W s r ≫ innerNerveRowsMiddle (C:=C) r u := by
  apply NatTrans.ext; funext p
  exact tripleResolutionAugmentation_middle_natural W p.unop.len r u
lemma innerRowsMiddle_id (q r:ℕ) : innerRowsMiddle W r (OrderHom.id (α:=Fin (q+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  have he : tripleMiddleReindex W p.unop.len r (OrderHom.id (α:=Fin (q+1))) = 𝟙 _ := by
    apply NatTrans.ext; funext n; apply Cat.ext
    exact Diagram.map_reindex_id
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,CategoryTheory.Functor.map_id]
  rfl
lemma innerRowsMiddle_comp (r:ℕ) {p q s:ℕ}
    (u:Fin (p+1)→oFin (q+1)) (v:Fin (q+1)→oFin (s+1)) :
    innerRowsMiddle W r (v.comp u) = innerRowsMiddle W r v ≫ innerRowsMiddle W r u := by
  apply NatTrans.ext; funext n
  have he : tripleMiddleReindex W n.unop.len r (v.comp u) =
      tripleMiddleReindex W n.unop.len r v ≫ tripleMiddleReindex W n.unop.len r u := by
    apply NatTrans.ext; funext k; apply Cat.ext
    exact Diagram.map_reindex_comp u v
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,Functor.map_comp]
  rfl
noncomputable def middleResolutionRows (r:ℕ) : SimplicialObject SSet where
  obj q := SimplicialDiagonal.diagonal.obj (innerResolutionRows W q.unop.len r)
  map f := SimplicialDiagonal.diagonal.map (innerRowsMiddle W r f.unop.toOrderHom)
  map_id q := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W r (OrderHom.id (α:=Fin (q.unop.len+1)))) = _
    rw [innerRowsMiddle_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W r (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [innerRowsMiddle_comp,Functor.map_comp]

lemma innerNerveRowsMiddle_id (q r:ℕ) :
    innerNerveRowsMiddle (C:=C) r (OrderHom.id (α:=Fin (q+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram C (Fin (p.unop.len+1)))
    (OrderHom.id (α:=Fin (q+1))))) = _
  rw [Diagram.map_reindex_id]
  rfl
lemma innerNerveRowsMiddle_comp (r:ℕ) {p q s:ℕ}
    (u:Fin (p+1)→oFin (q+1)) (v:Fin (q+1)→oFin (s+1)) :
    innerNerveRowsMiddle (C:=C) r (v.comp u) =
      innerNerveRowsMiddle (C:=C) r v ≫ innerNerveRowsMiddle (C:=C) r u := by
  apply NatTrans.ext; funext n
  change nerveMap (Diagram.map (I:=Fin (r+1)) (Diagram.reindex (C:=Diagram C (Fin (n.unop.len+1)))
    (v.comp u))) = _
  rw [Diagram.map_reindex_comp]
  rfl
noncomputable def middleNerveRows (r:ℕ) : SimplicialObject SSet where
  obj q := SimplicialDiagonal.diagonal.obj (innerNerveRows (C:=C) q.unop.len r)
  map f := SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) r f.unop.toOrderHom)
  map_id q := by
    change SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) r (OrderHom.id (α:=Fin (q.unop.len+1)))) = _
    rw [innerNerveRowsMiddle_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) r (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [innerNerveRowsMiddle_comp,Functor.map_comp]
noncomputable def middleResolutionAugmentation (r:ℕ) :
    middleResolutionRows W r ⟶ middleNerveRows (C:=C) r where
  app q := SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W q.unop.len r)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W r f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W m.unop.len r) = _
    rw [←Functor.map_comp,innerResolutionAugmentation_middle_natural,Functor.map_comp]
    rfl
noncomputable instance middleResolutionTotal_isIso (r j:ℕ) :
    IsIso (SSet.homologyMap
      (SimplicialDiagonal.diagonal.map (middleResolutionAugmentation W r))
      DiagonalResolution.Z j) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p n
  exact innerResolutionTotal_isIso W p.unop.len r n

lemma tripleInnerOuter_commute (q:ℕ) {p s r t:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    tripleInnerReindex W q t u ≫ tripleOuterReindex W p q v =
      tripleOuterReindex W s q v ≫ tripleInnerReindex W q r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact (Diagram.reindex_map (Diagram.map (Diagram.reindex u)) v).symm
lemma tripleMiddleOuter_commute (p:ℕ) {q s r t:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    tripleMiddleReindex W p t u ≫ tripleOuterReindex W p q v =
      tripleOuterReindex W p s v ≫ tripleMiddleReindex W p r u := by
  apply NatTrans.ext; funext n; apply Cat.ext
  exact (Diagram.reindex_map (Diagram.reindex u) v).symm
noncomputable def innerRowsOuter (q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    innerResolutionRows W q s ⟶ innerResolutionRows W q r where
  app p := SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p.unop.len q u)
  naturality n m f := by
    change SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q s f.unop.toOrderHom) ≫
      SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W m.unop.len q u) = _
    rw [←Functor.map_comp,tripleInnerOuter_commute,Functor.map_comp]
    rfl
noncomputable def innerNerveRowsOuter (q:ℕ) {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    innerNerveRows (C:=C) q s ⟶ innerNerveRows (C:=C) q r where
  app p := nerveMap (Diagram.reindex (C:=Diagram (Diagram C (Fin (p.unop.len+1))) (Fin (q+1))) u)
  naturality n m f := by
    change nerveMap (Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)) ⋙
      Diagram.reindex u) = nerveMap (Diagram.reindex u ⋙
      Diagram.map (Diagram.map (Diagram.reindex f.unop.toOrderHom)))
    rw [Diagram.reindex_map]
lemma innerResolutionAugmentation_outer_natural (q:ℕ) {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) :
    innerRowsOuter W q u ≫ innerResolutionAugmentation W q r =
      innerResolutionAugmentation W q s ≫ innerNerveRowsOuter (C:=C) q u := by
  apply NatTrans.ext; funext p
  exact tripleResolutionAugmentation_outer_natural W p.unop.len q u
lemma innerRowsMiddleOuter_commute {q s r t:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    innerRowsMiddle W t u ≫ innerRowsOuter W q v =
      innerRowsOuter W s v ≫ innerRowsMiddle W r u := by
  apply NatTrans.ext; funext p
  change SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p.unop.len t u) ≫
      SimplicialDiagonal.nerveDiagonal.map (tripleOuterReindex W p.unop.len q v) = _
  rw [←Functor.map_comp,tripleMiddleOuter_commute,Functor.map_comp]
  rfl
lemma innerNerveRowsMiddleOuter_commute {q s r t:ℕ}
    (u:Fin (q+1)→oFin (s+1)) (v:Fin (r+1)→oFin (t+1)) :
    innerNerveRowsMiddle (C:=C) t u ≫ innerNerveRowsOuter (C:=C) q v =
      innerNerveRowsOuter (C:=C) s v ≫ innerNerveRowsMiddle (C:=C) r u := by
  apply NatTrans.ext; funext p
  change nerveMap (Diagram.map (Diagram.reindex u) ⋙ Diagram.reindex v) =
    nerveMap (Diagram.reindex v ⋙ Diagram.map (Diagram.reindex u))
  rw [Diagram.reindex_map]
noncomputable def middleRowsOuter {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    middleResolutionRows W s ⟶ middleResolutionRows W r where
  app q := SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len u)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (innerRowsMiddle W s f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (innerRowsOuter W m.unop.len u) = _
    rw [←Functor.map_comp,innerRowsMiddleOuter_commute,Functor.map_comp]
    rfl
noncomputable def middleNerveRowsOuter {r s:ℕ} (u:Fin (r+1)→oFin (s+1)) :
    middleNerveRows (C:=C) s ⟶ middleNerveRows (C:=C) r where
  app q := SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) q.unop.len u)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (innerNerveRowsMiddle (C:=C) s f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) m.unop.len u) = _
    rw [←Functor.map_comp,innerNerveRowsMiddleOuter_commute,Functor.map_comp]
    rfl
lemma middleResolutionAugmentation_outer_natural {r s:ℕ}
    (u:Fin (r+1)→oFin (s+1)) :
    middleRowsOuter W u ≫ middleResolutionAugmentation W r =
      middleResolutionAugmentation W s ≫ middleNerveRowsOuter (C:=C) u := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len u) ≫
    SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W q.unop.len r) = _
  rw [←Functor.map_comp,innerResolutionAugmentation_outer_natural,Functor.map_comp]
  rfl

lemma innerRowsOuter_id (q r:ℕ) : innerRowsOuter W q (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  have he : tripleOuterReindex W p.unop.len q (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
    apply NatTrans.ext; funext n; apply Cat.ext
    exact Diagram.reindex_id
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,CategoryTheory.Functor.map_id]
  rfl
lemma innerRowsOuter_comp (q:ℕ) {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    innerRowsOuter W q (v.comp u) = innerRowsOuter W q v ≫ innerRowsOuter W q u := by
  apply NatTrans.ext; funext n
  have he : tripleOuterReindex W n.unop.len q (v.comp u) =
      tripleOuterReindex W n.unop.len q v ≫ tripleOuterReindex W n.unop.len q u := by
    apply NatTrans.ext; funext k; apply Cat.ext
    exact Diagram.reindex_comp u v
  change SimplicialDiagonal.nerveDiagonal.map _ = _
  rw [he,Functor.map_comp]
  rfl
lemma middleRowsOuter_id (r:ℕ) : middleRowsOuter W (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len (OrderHom.id (α:=Fin (r+1)))) = _
  rw [innerRowsOuter_id,CategoryTheory.Functor.map_id]
  rfl
lemma middleRowsOuter_comp {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    middleRowsOuter W (v.comp u) = middleRowsOuter W v ≫ middleRowsOuter W u := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerRowsOuter W q.unop.len (v.comp u)) = _
  rw [innerRowsOuter_comp,Functor.map_comp]
  rfl
lemma innerNerveRowsOuter_id (q r:ℕ) :
    innerNerveRowsOuter (C:=C) q (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext p
  change nerveMap (Diagram.reindex (C:=Diagram (Diagram C (Fin (p.unop.len+1))) (Fin (q+1)))
    (OrderHom.id (α:=Fin (r+1)))) = _
  rw [Diagram.reindex_id]
  rfl
lemma innerNerveRowsOuter_comp (q:ℕ) {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    innerNerveRowsOuter (C:=C) q (v.comp u) =
      innerNerveRowsOuter (C:=C) q v ≫ innerNerveRowsOuter (C:=C) q u := by
  apply NatTrans.ext; funext n
  change nerveMap (Diagram.reindex (C:=Diagram (Diagram C (Fin (n.unop.len+1))) (Fin (q+1)))
    (v.comp u)) = _
  rw [Diagram.reindex_comp]
  rfl
lemma middleNerveRowsOuter_id (r:ℕ) :
    middleNerveRowsOuter (C:=C) (OrderHom.id (α:=Fin (r+1))) = 𝟙 _ := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) q.unop.len (OrderHom.id (α:=Fin (r+1)))) = _
  rw [innerNerveRowsOuter_id,CategoryTheory.Functor.map_id]
  rfl
lemma middleNerveRowsOuter_comp {p r s:ℕ}
    (u:Fin (p+1)→oFin (r+1)) (v:Fin (r+1)→oFin (s+1)) :
    middleNerveRowsOuter (C:=C) (v.comp u) =
      middleNerveRowsOuter (C:=C) v ≫ middleNerveRowsOuter (C:=C) u := by
  apply NatTrans.ext; funext q
  change SimplicialDiagonal.diagonal.map (innerNerveRowsOuter (C:=C) q.unop.len (v.comp u)) = _
  rw [innerNerveRowsOuter_comp,Functor.map_comp]
  rfl
noncomputable def outerResolutionRows : SimplicialObject SSet where
  obj r := SimplicialDiagonal.diagonal.obj (middleResolutionRows W r.unop.len)
  map f := SimplicialDiagonal.diagonal.map (middleRowsOuter W f.unop.toOrderHom)
  map_id r := by
    change SimplicialDiagonal.diagonal.map (middleRowsOuter W (OrderHom.id (α:=Fin (r.unop.len+1)))) = _
    rw [middleRowsOuter_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (middleRowsOuter W (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [middleRowsOuter_comp,Functor.map_comp]
noncomputable def outerNerveRows : SimplicialObject SSet where
  obj r := SimplicialDiagonal.diagonal.obj (middleNerveRows (C:=C) r.unop.len)
  map f := SimplicialDiagonal.diagonal.map (middleNerveRowsOuter (C:=C) f.unop.toOrderHom)
  map_id r := by
    change SimplicialDiagonal.diagonal.map (middleNerveRowsOuter (C:=C) (OrderHom.id (α:=Fin (r.unop.len+1)))) = _
    rw [middleNerveRowsOuter_id,CategoryTheory.Functor.map_id]
  map_comp f g := by
    change SimplicialDiagonal.diagonal.map (middleNerveRowsOuter (C:=C) (f.unop.toOrderHom.comp g.unop.toOrderHom)) = _
    rw [middleNerveRowsOuter_comp,Functor.map_comp]
noncomputable def outerResolutionAugmentation :
    outerResolutionRows W ⟶ outerNerveRows (C:=C) where
  app r := SimplicialDiagonal.diagonal.map (middleResolutionAugmentation W r.unop.len)
  naturality n m f := by
    change SimplicialDiagonal.diagonal.map (middleRowsOuter W f.unop.toOrderHom) ≫
      SimplicialDiagonal.diagonal.map (middleResolutionAugmentation W m.unop.len) = _
    rw [←Functor.map_comp,middleResolutionAugmentation_outer_natural,Functor.map_comp]
    rfl

noncomputable instance tripleResolutionTotal_isIso (j:ℕ) :
    IsIso (SSet.homologyMap
      (SimplicialDiagonal.diagonal.map (outerResolutionAugmentation W))
      DiagonalResolution.Z j) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p n
  exact middleResolutionTotal_isIso W p.unop.len n
end

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma reverseDiagonalReindex {I J:Type} [Preorder I] [Preorder J] (u:I→oJ) :
    Diagram.reindex (C:=Diagram (Diagram C J) J) u ⋙
      Diagram.map (I:=I) (Diagram.reindex (C:=Diagram C J) u) ⋙
      Diagram.map (I:=I) (Diagram.map (I:=I) (Diagram.reindex (C:=C) u)) =
        diagonalReindex (C:=C) u := by
  unfold diagonalReindex
  rw [←Functor.assoc,Diagram.reindex_map,Functor.assoc]
  rw [Diagram.reindex_map]
  rw [←Functor.assoc,←Diagram.map_map_reindex,Functor.assoc]
noncomputable def totalNerveBarIso :
    SimplicialDiagonal.diagonal.obj (outerNerveRows (C:=C)) ≅ bar₃ (C:=C) :=
  NatIso.ofComponents (fun _=>Iso.refl _) (by
    intro n m f
    ext x
    exact congrArg (fun F => f.unop.toOrderHom.toFunctor ⋙ x ⋙ F)
      (reverseDiagonalReindex (C:=C) f.unop.toOrderHom))
variable (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [W.IsStableUnderBraiding]
noncomputable def totalStringToBar :
    SimplicialDiagonal.diagonal.obj (outerResolutionRows W) ⟶ bar₃ (C:=C) :=
  SimplicialDiagonal.diagonal.map (outerResolutionAugmentation W) ≫ totalNerveBarIso.hom
noncomputable instance totalStringToBar_isIso (j:ℕ) :
    IsIso (SSet.homologyMap (totalStringToBar W) DiagonalResolution.Z j) := by
  unfold totalStringToBar
  rw [SSet.homologyMap_comp]
  have := tripleResolutionTotal_isIso W j
  infer_instance
end RestrictedNerve

end

namespace SimpleAmenable.PolygonObject
open _root_.CategoryTheory _root_.OAI.CategoryTheory

instance positionalPropertyInverse (a:ℕ) : Fact (positionalProperty a).StableUnderInverse where
  out := by
    intro U V e h
    change Positional e.hom at h
    change Positional e.inv
    have hi := positional_inv h
    simpa using hi

noncomputable def tripleStringToBar (a:ℕ) :
    SimplicialDiagonal.diagonal.obj (RestrictedNerve.outerResolutionRows (positionalProperty a)) ⟶
      IntervalBar.Diagram.bar₃ (C:=PolygonObject a) :=
  RestrictedNerve.totalStringToBar (positionalProperty a)
noncomputable instance tripleStringToBar_isIso (a j:ℕ) :
    IsIso (SSet.homologyMap (tripleStringToBar a) DiagonalResolution.Z j) :=
  RestrictedNerve.totalStringToBar_isIso (positionalProperty a) j
end SimpleAmenable.PolygonObject

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable def stringBarRows : SimplicialObject SSet where
  obj n := bar₃ (C:=Strings W n.unop.len)
  map f := bar₃Map (reindex W f.unop.toOrderHom.toFunctor)
  map_id n := by
    ext k x
    exact congrArg (fun F => x ⋙ F)
      (map₃_strings_reindex_id W n.unop.len k.unop.len k.unop.len k.unop.len)
  map_comp f g := by
    ext k x
    exact congrArg (fun F => x ⋙ F)
      (map₃_strings_reindex_comp W k.unop.len k.unop.len k.unop.len
        g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor)

noncomputable def stringBarTotalComponent (n:SimplexCategoryᵒᵖ) :
    (SimplicialDiagonal.diagonal.obj (stringBarRows W)).obj n ≅
      (SimplicialDiagonal.diagonal.obj (outerResolutionRows W)).obj n := Iso.refl _
end RestrictedNerve

end OAI
