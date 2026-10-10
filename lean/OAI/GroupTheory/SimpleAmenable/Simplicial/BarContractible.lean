import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IteratedBarMaps
import OAI.GroupTheory.SimpleAmenable.Homology.CanonicalProduct
import OAI.GroupTheory.SimpleAmenable.Simplicial.SimplicialH0

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits SimplicialObject Simplicial Opposite MonoidalCategory
namespace SimplicialDiagonal
open FreeChains

lemma connected_of_iso {X Y : SSet} (e : X ≅ Y) [Y.IsConnected] : X.IsConnected where
  allEq u v := by
    have h := congrArg (SSet.mapπ₀ e.inv) (Subsingleton.elim (SSet.mapπ₀ e.hom u) (SSet.mapπ₀ e.hom v))
    simpa only [←SSet.mapπ₀_comp_apply,Iso.hom_inv_id,SSet.mapπ₀_id_apply] using h
  nonempty := ⟨e.inv.app _ (Classical.arbitrary _)⟩
lemma connectivity (X : I ⥤ SSet) (d : ℕ)
    (hc : ∀ p,(X.obj p).IsConnected)
    (hz : ∀ q,0<q → IsZero (SSet.homology (C:=A) (X.obj (op ⦋0⦌)) Z q))
    (hr : ∀ p q,0<q → q<d → IsZero (SSet.homology (C:=A) (X.obj (op ⦋p⦌)) Z q))
    (n : ℕ) (hn : 0<n) (hd : n<d+1) : IsZero (SSet.homology (C:=A) (diagonal.obj X) Z n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply BarHomology.connectivity (uncurry X) d
  · intro p
    have := hc p
    exact connected_of_iso (rowIso X p)
  · intro q hq
    exact IsZero.of_iso (hz q hq) ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋0⦌)))
  · intro p q hq hqd
    exact IsZero.of_iso (hr p q hq hqd) ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋p⦌)))
  · exact hn
  · exact hd
end SimplicialDiagonal
namespace CategoryTheory.nerve
open scoped _root_.CategoryTheory _root_.CategoryTheory.nerve
open FreeChains

lemma const_map {C : Type} [_root_.CategoryTheory.Category.{0} C] (c : C) :
    _root_.CategoryTheory.nerveMap ((_root_.CategoryTheory.Functor.const C).obj c) = SSet.const (nerveEquiv.symm c) := by
  ext n x
  rfl
lemma positive_zero {C : Type} [_root_.CategoryTheory.Category.{0} C] [Nonempty C]
    [∀ x y : C,Subsingleton (x ⟶ y)] (hh : ∀ x y : C,Nonempty (x ⟶ y))
    (n : ℕ) (hn : n≠0) : IsZero (SSet.homology (C:=A) (_root_.CategoryTheory.nerve C) Z n) := by
  let c := Classical.arbitrary C
  let α : 𝟭 C ⟶ (_root_.CategoryTheory.Functor.const C).obj c :=
    { app x := Classical.choice (hh x c)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have h := (NerveHomotopy.ofNatTrans α).congr_homologyMap Z n
  change SSet.homologyMap (𝟙 (_root_.CategoryTheory.nerve C)) Z n = SSet.homologyMap (_root_.CategoryTheory.nerveMap ((_root_.CategoryTheory.Functor.const C).obj c)) Z n at h
  erw [SSet.homologyMap_id,const_map,ConnectedProduct.const_homology_zero _ n hn] at h
  exact (IsZero.iff_id_eq_zero _).mpr h
end CategoryTheory.nerve
namespace IntervalBar.Diagram
open FreeChains

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
instance zero_thin (X Y : Diagram C (Fin 1)) : Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => (eval 0).map_injective (funext (fun i => Fin.elim0 i))⟩
instance zero_hom_nonempty (X Y : Diagram C (Fin 1)) : Nonempty (X ⟶ Y) := ⟨zeroHom C X Y⟩
instance hom_thin [∀ x y : C,Subsingleton (x ⟶ y)] (n : ℕ)
    (X Y : Diagram C (Fin (n+1))) : Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => Hom.ext (fun _ _ _ => Subsingleton.elim _ _)⟩
noncomputable def homOfAll (hh : ∀ x y : C,Nonempty (x ⟶ y)) (n : ℕ)
    (X Y : Diagram C (Fin (n+1))) : X ⟶ Y :=
  (eval n).preimage (fun _ => Classical.choice (hh _ _))
omit [SymmetricCategory C] in
lemma bar_acyclic [∀ x y : C,Subsingleton (x ⟶ y)]
    (hh : ∀ x y : C,Nonempty (x ⟶ y)) (n : ℕ) (hn : 0<n) :
    IsZero (SSet.homology (C:=A) (bar (C:=C)) Z n) := by
  let X := (((Functor.whiskeringRight SimplicialDiagonal.I Cat SSet).obj nerveFunctor).obj (simplicial (C:=C)))
  have hc (p : SimplicialDiagonal.I) : (X.obj p).IsConnected := by
    have : Nonempty (Diagram C (Fin (p.unop.len+1))) := ⟨constantUnit⟩
    change (nerve (Diagram C (Fin (p.unop.len+1)))).IsConnected
    exact nerve.connected_of_hom (fun x y => ⟨homOfAll hh _ x y⟩)
  have hz (p : ℕ) (q : ℕ) (hq : 0<q) : IsZero (SSet.homology (C:=A) (X.obj (op ⦋p⦌)) Z q) := by
    have : Nonempty (Diagram C (Fin (p+1))) := ⟨constantUnit⟩
    exact nerve.positive_zero (fun x y => ⟨homOfAll hh p x y⟩) q (by omega)
  exact SimplicialDiagonal.connectivity X n hc (hz 0) (fun p q hq _ => hz p q hq) n hn (by omega)
lemma zero_bar_acyclic (n : ℕ) (hn : 0<n) :
    IsZero (SSet.homology (C:=A) (bar (C:=Diagram C (Fin 1))) Z n) :=
  bar_acyclic (fun _ _ => inferInstance) n hn
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K L M : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L] [Preorder M]
private lemma map_map_reindex_unit_app (f : I →o J)
    (A : Diagram (Diagram (Diagram C J) L) M) (i : M)
    (j k : L) (h : j ≤ k) (l m : I) (hlm : l ≤ m) :
    ((((map (map (reindex f))).obj A).unit i).hom.app j k h).app l m hlm =
      ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) := by
  change (((map (reindex f)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (map (reindex f))).app j k h).app l m hlm = _
  erw [comp_app, map_η_app (I:=L) (reindex (C:=C) f)]
  change ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma map_map_reindex_comp (f : I →o J) (g : J →o K) :
    map (I:=M) (map (I:=L) (reindex (C:=C) (g.comp f))) =
      map (map (reindex g)) ⋙ map (map (reindex f)) := by
  have he (X : Diagram (Diagram C K) L) : mapObj (reindex (g.comp f)) X=
      mapObj (reindex f) (mapObj (reindex g) X) :=
    congrArg (fun F => F.obj X) (map_reindex_comp f g)
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply hom_hext rfl rfl
      intro l m hlm
      apply heq_of_eq
      erw [map_map_reindex_unit_app, map_map_reindex_unit_app, map_map_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      intro l m hlm
      apply hom_hext rfl rfl
      intro n p hnp
      apply heq_of_eq
      change 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app (g (f n)) (g (f p)) _ =
        𝟙 _ ≫ (𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app (g (f n)) (g (f p)) _)
      simp only [Category.id_comp]
  · intro A B h
    apply Hom.ext; intro i j hij
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro k l hkl
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro m n hmn
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
lemma barMap_map_reindex_id : barMap (map (I:=J) (reindex (C:=C) (OrderHom.id (α:=I))))=𝟙 _ := by
  have he : simplicialMap (map (I:=J) (reindex (C:=C) (OrderHom.id (α:=I))))=𝟙 _ := by
    apply NatTrans.ext; funext p; apply Cat.ext
    exact map_map_reindex_id
  simp only [barMap,he]
  rfl
lemma barMap_map_reindex_comp (f : I →o J) (g : J →o K) :
    barMap (map (I:=L) (reindex (C:=C) (g.comp f))) =
      barMap (map (reindex g)) ≫ barMap (map (reindex f)) := by
  have he : simplicialMap (map (I:=L) (reindex (C:=C) (g.comp f))) =
      simplicialMap (map (reindex g)) ≫ simplicialMap (map (reindex f)) := by
    apply NatTrans.ext; funext p; apply Cat.ext
    exact map_map_reindex_comp f g
  simp only [barMap,he,Functor.map_comp]
  rfl
lemma bar₂Map_reindex_id : bar₂Map (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
  have he : rows₂Map (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
    apply NatTrans.ext; funext p
    exact barMap_map_reindex_id
  simp only [bar₂Map,he]
  rfl
lemma bar₂Map_reindex_comp (f : I →o J) (g : J →o K) :
    bar₂Map (reindex (C:=C) (g.comp f)) = bar₂Map (reindex g) ≫ bar₂Map (reindex f) := by
  have he : rows₂Map (reindex (C:=C) (g.comp f)) = rows₂Map (reindex g) ≫ rows₂Map (reindex f) := by
    apply NatTrans.ext; funext p
    exact barMap_map_reindex_comp f g
  simp only [bar₂Map,he,Functor.map_comp]
  rfl
noncomputable def rows₃ : SimplexCategoryᵒᵖ ⥤ SSet where
  obj p := bar₂ (C:=Diagram C (Fin (p.unop.len+1)))
  map f := bar₂Map (reindex f.unop.toOrderHom)
  map_id _ := bar₂Map_reindex_id
  map_comp f g := bar₂Map_reindex_comp g.unop.toOrderHom f.unop.toOrderHom
noncomputable def bar₃ : SSet := SimplicialDiagonal.diagonal.obj (rows₃ (C:=C))
instance bar₃_connected : (bar₃ (C:=C)).IsConnected := by
  have : ((rows₃ (C:=C)).obj (op ⦋0⦌)).IsConnected := bar₂_connected
  exact SimplicialDiagonal.diagonal_connected (rows₃ (C:=C))
open FreeChains
lemma bar₂_acyclic [∀ x y : C,Subsingleton (x ⟶ y)]
    (hh : ∀ x y : C,Nonempty (x ⟶ y)) (n : ℕ) (hn : 0<n) :
    Limits.IsZero (SSet.homology (C:=A) (bar₂ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₂ (C:=C)) n
  · intro _; exact bar_connected _
  · intro q hq
    exact bar_acyclic (fun x y => ⟨homOfAll hh 0 x y⟩) q hq
  · intro p q hq _
    exact bar_acyclic (fun x y => ⟨homOfAll hh p x y⟩) q hq
  · exact hn
  · omega
lemma bar₂_H1_zero (n : ℕ) (hn : 0<n) (hd : n<2) :
    Limits.IsZero (SSet.homology (C:=A) (bar₂ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₂ (C:=C)) 1
  · intro _; exact bar_connected _
  · exact zero_bar_acyclic
  · intro p q hq hd; omega
  · exact hn
  · exact hd
lemma bar₃_low_zero (n : ℕ) (hn : 0<n) (hd : n<3) :
    Limits.IsZero (SSet.homology (C:=A) (bar₃ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₃ (C:=C)) 2
  · intro _; exact bar₂_connected
  · intro q hq
    change Limits.IsZero (SSet.homology (C:=A) (bar₂ (C:=Diagram C (Fin 1))) Z q)
    exact bar₂_acyclic (fun _ _ => inferInstance) q hq
  · intro _ q hq hd; exact bar₂_H1_zero q hq hd
  · exact hn
  · exact hd
end IntervalBar.Diagram

end OAI
