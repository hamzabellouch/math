import Mathlib
import OAI.CategoryTheory.Thomason.Cones

namespace OAI

/-! Presentations. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def coneOld (B : OmegaCategory.{u}) (x : (zeroFiber (coneLabel B)).Cell) : B.Cell :=
  match x with
  | ⟨ConeCell.old y, _⟩ => y
  | ⟨ConeCell.edge _, h⟩ => (interval_arrow_ne_zero h).elim
  | ⟨ConeCell.top, h⟩ => (interval_one_ne_zero h).elim

@[simp] lemma coneOld_old (B : OmegaCategory.{u}) (x : B.Cell) (h) :
    coneOld B ⟨ConeCell.old x, h⟩ = x := rfl

lemma old_coneOld (B : OmegaCategory.{u}) (x : (zeroFiber (coneLabel B)).Cell) :
    ConeCell.old (coneOld B x) = x.val := by
  rcases x with ⟨x, hx⟩
  cases x with
  | old y => rfl
  | edge a => exact (interval_arrow_ne_zero hx).elim
  | top => exact (interval_one_ne_zero hx).elim

def coneOldFunctor (B : OmegaCategory.{u}) : Functor (zeroFiber (coneLabel B)) B where
  map := coneOld B
  map_source k x := by
    apply ConeCell.old.inj
    change ConeCell.old (coneOld B ((zeroFiber (coneLabel B)).source k x)) =
      B.terminalCone.source k (ConeCell.old (coneOld B x))
    rw [old_coneOld, old_coneOld]
    rfl
  map_target k x := by
    apply ConeCell.old.inj
    change ConeCell.old (coneOld B ((zeroFiber (coneLabel B)).target k x)) =
      B.terminalCone.target k (ConeCell.old (coneOld B x))
    rw [old_coneOld, old_coneOld]
    rfl
  map_comp k x y h h' := by
    apply ConeCell.old.inj
    rw [old_coneOld]
    change B.terminalCone.comp k x.val y.val _ =
      B.terminalCone.comp k (ConeCell.old (coneOld B x)) (ConeCell.old (coneOld B y))
        (congrArg ConeCell.old h')
    congr 1
    · exact (old_coneOld B x).symm
    · exact (old_coneOld B y).symm

def coneRestrict {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (H : Functor C B.terminalCone)
    (hw : Functor.comp H (coneLabel B) = p) : Functor (zeroFiber p) B :=
  Functor.comp (Functor.fiberMap p (coneLabel B) H hw (intervalVertex 0)) (coneOldFunctor B)

lemma old_coneRestrict {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (H : Functor C B.terminalCone)
    (hw : Functor.comp H (coneLabel B) = p) (x : (zeroFiber p).Cell) :
    ConeCell.old ((coneRestrict p H hw).map x) = H.map x.val :=
  old_coneOld B _

lemma coneRestrict_extend {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (F : Functor (zeroFiber p) B) :
    coneRestrict p (coneExtend p F) (coneExtend_label p F) = F := by
  apply Functor.ext
  funext x
  apply ConeCell.old.inj
  rw [old_coneRestrict]
  exact coneExtendMap_zero p F x.val x.property

lemma coneExtend_restrict {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (H : Functor C B.terminalCone)
    (hw : Functor.comp H (coneLabel B) = p) :
    coneExtend p (coneRestrict p H hw) = H := by
  apply Functor.ext
  funext x
  have hl : (coneLabel B).map (H.map x) = p.map x := congrArg (fun f => f.map x) hw
  change coneExtendMap p (coneRestrict p H hw) x = H.map x
  generalize he : H.map x = y at hl ⊢
  cases y with
  | old y =>
    rw [coneExtendMap_zero p _ x hl.symm]
    exact (old_coneRestrict p H hw ⟨x, hl.symm⟩).trans he
  | edge a =>
    rw [coneExtendMap_arrow p _ x hl.symm]
    apply congrArg ConeCell.edge
    apply Subtype.ext
    apply ConeCell.old.inj
    change ConeCell.old ((coneRestrict p H hw).map _) = ConeCell.old a.val
    rw [old_coneRestrict]
    change H.map (C.source 0 x) = ConeCell.old a.val
    rw [H.map_source, he]
    rfl
  | top => exact coneExtendMap_one p _ x hl.symm

open CategoryTheory

noncomputable def zeroFiberConeHomEquiv (p : CategoryTheory.Over interval.{u})
    (B : OmegaCategory.{u}) :
    ((fiberFunctor (intervalVertex 0)).obj p ⟶ B) ≃ (p ⟶ terminalConeFunctor.obj B) where
  toFun F := CategoryTheory.Over.homMk (coneExtend p.hom F) (coneExtend_label p.hom F)
  invFun H := coneRestrict p.hom H.left (CategoryTheory.Over.w H)
  left_inv := coneRestrict_extend p.hom
  right_inv H := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact coneExtend_restrict p.hom H.left (CategoryTheory.Over.w H)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

noncomputable def zeroFiberConeAdjunction : CategoryTheory.Adjunction
    (fiberFunctor (intervalVertex 0)) terminalConeFunctor.{u} :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := zeroFiberConeHomEquiv
    homEquiv_naturality_left_symm := by
      intro p' p B F G
      rfl
    homEquiv_naturality_right := by
      intro p B D F G
      apply CategoryTheory.Over.OverMorphism.ext
      apply Functor.ext
      funext x
      change Functor (zeroFiber p.hom) B at F
      change Functor B D at G
      change coneExtendMap p.hom (Functor.comp F G) x =
        (coneMap G).map (coneExtendMap p.hom F x)
      rcases interval_cases (p.hom.map x) with hx | hx | hx
      · rw [coneExtendMap_zero p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_zero p.hom F x hx)).symm
      · rw [coneExtendMap_arrow p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_arrow p.hom F x hx)).symm
      · rw [coneExtendMap_one p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_one p.hom F x hx)).symm }

noncomputable instance zeroFiber_preservesColimits :
    CategoryTheory.Limits.PreservesColimitsOfSize.{v,w} (fiberFunctor.{u} (intervalVertex 0)) :=
  zeroFiberConeAdjunction.leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


namespace CellTerm


end CellTerm


namespace Presentation

variable (P : Presentation.{u})


namespace Equiv

variable {P} {x y z x' y' : CellTerm P.Generator}

@[refl] lemma refl (x : CellTerm P.Generator) : P.Equiv x x := fun _ _ => rfl
@[symm] lemma symm (h : P.Equiv x y) : P.Equiv y x := fun C I => (h C I).symm
@[trans] lemma trans (h : P.Equiv x y) (h' : P.Equiv y z) : P.Equiv x z :=
  fun C I => (h C I).trans (h' C I)
lemma source (k : ℕ) (h : P.Equiv x y) : P.Equiv (.source k x) (.source k y) :=
  fun C I => congrArg (C.source k) (h C I)
lemma target (k : ℕ) (h : P.Equiv x y) : P.Equiv (.target k x) (.target k y) :=
  fun C I => congrArg (C.target k) (h C I)
lemma composable_congr (k : ℕ) (hx : P.Equiv x x') (hy : P.Equiv y y') :
    P.Equiv (.target k x) (.source k y) ↔ P.Equiv (.target k x') (.source k y') :=
  ⟨fun h => (hx.target k).symm.trans (h.trans (hy.source k)),
   fun h => (hx.target k).trans (h.trans (hy.source k).symm)⟩
lemma comp (k : ℕ) (hx : P.Equiv x x') (hy : P.Equiv y y') :
    P.Equiv (.comp k x y) (.comp k x' y') := by
  intro C I
  exact congrArg₂ (CellTerm.composeOrLeft C k) (hx C I) (hy C I)

end Equiv


lemma eval_dimension {x : CellTerm P.Generator} (hx : P.Valid x)
    (C : OmegaCategory.{u}) (I : P.Interpretation C) :
    C.source (x.dimension P.dimension) (x.eval C I.map) = x.eval C I.map := by
  induction hx with
  | gen g => exact I.bounded g
  | source k x hx ih => exact C.source_source_self k _
  | target k x hx ih => exact C.source_target_self k _
  | comp k x y hx hy h ihx ihy =>
    have hm := h C I
    change C.target k (x.eval C I.map) = C.source k (y.eval C I.map) at hm
    simp only [CellTerm.dimension, CellTerm.eval, CellTerm.composeOrLeft, dite_eq_left hm]
    have hkn : k < max (k+1) (max (x.dimension P.dimension) (y.dimension P.dimension)) := by omega
    rw [C.source_comp_gt _ k hkn _ _ hm (C.source_composable hkn hm)]
    congr 1
    · exact C.source_fixed_upwards (by omega) ihx
    · exact C.source_fixed_upwards (by omega) ihy


lemma compTerm_equiv (k : ℕ) {x y x' y' : P.ValidTerm}
    (hx : P.Equiv x.val x'.val) (hy : P.Equiv y.val y'.val) :
    P.Equiv (P.compTerm k x y).val (P.compTerm k x' y').val := by
  classical
  have he := Equiv.composable_congr k hx hy
  by_cases h : P.Equiv (.target k x.val) (.source k y.val)
  · simp only [compTerm, dite_eq_left h, dite_eq_left (he.mp h)]
    exact Equiv.comp k hx hy
  · simp only [compTerm, dite_eq_right h, dite_eq_right (mt he.mpr h)]
    exact hx


lemma cells_ext {x y : P.Cells}
    (h : ∀ (C : OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound h

@[simp] lemma evaluate_source (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
    P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
  induction x using Quotient.inductionOn
  rfl

@[simp] lemma evaluate_target (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
    P.evaluate C I (P.target k x) = C.target k (P.evaluate C I x) := by
  induction x using Quotient.inductionOn
  rfl

lemma evaluate_composable (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
    (x y : P.Cells) (h : P.target k x = P.source k y) :
    C.target k (P.evaluate C I x) = C.source k (P.evaluate C I y) := by
  rw [← evaluate_target, ← evaluate_source, h]

@[simp] lemma evaluate_comp (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
    (x y : P.Cells) (h : P.target k x = P.source k y) :
    P.evaluate C I (P.comp k x y h) =
      C.comp k (P.evaluate C I x) (P.evaluate C I y) (P.evaluate_composable C I k x y h) := by
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      have hm : P.Equiv (.target k x.val) (.source k y.val) := Quotient.exact h
      change (P.compTerm k x y).val.eval C I.map = _
      have hm' : C.target k (x.val.eval C I.map) = C.source k (y.val.eval C I.map) := hm C I
      simp only [compTerm, dite_eq_left hm, CellTerm.eval, CellTerm.composeOrLeft, dite_eq_left hm']
      rfl

end Presentation
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

variable (P : Presentation.{u})


lemma generator_bounded (g : P.Generator) :
    P.category.source (P.dimension g) (P.generator g) = P.generator g := by
  apply P.cells_ext
  intro C I
  exact I.bounded g

@[simp] lemma lift_generator (C : OmegaCategory.{u}) (I : P.Interpretation C) (g : P.Generator) :
    (P.lift C I).map (P.generator g) = I.map g := rfl

lemma mk_source (k : ℕ) (x : P.ValidTerm) :
    P.source k (Quotient.mk _ x) = Quotient.mk _ (P.sourceTerm k x) := rfl

lemma mk_target (k : ℕ) (x : P.ValidTerm) :
    P.target k (Quotient.mk _ x) = Quotient.mk _ (P.targetTerm k x) := rfl

lemma mk_comp (k : ℕ) (x y : P.ValidTerm)
    (h : P.Equiv (.target k x.val) (.source k y.val))
    (h' : P.target k (Quotient.mk _ x) = P.source k (Quotient.mk _ y)) :
    P.comp k (Quotient.mk _ x) (Quotient.mk _ y) h' =
      Quotient.mk _ ⟨.comp k x.val y.val, Valid.comp (P := P) k x.val y.val x.property y.property h⟩ := by
  change Quotient.mk _ (P.compTerm k x y) = _
  simp only [compTerm, dite_eq_left h]

lemma functor_ext {C : OmegaCategory.{u}} {F G : Functor P.category C}
    (h : ∀ g, F.map (P.generator g) = G.map (P.generator g)) : F = G := by
  apply Functor.ext
  funext x
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x, hx⟩
    induction hx with
    | gen g => exact h g
    | source k x hx ih =>
      change F.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩)) =
        G.map (P.category.source k (Quotient.mk _ ⟨x, hx⟩))
      rw [F.map_source, G.map_source, ih]
    | target k x hx ih =>
      change F.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩)) =
        G.map (P.category.target k (Quotient.mk _ ⟨x, hx⟩))
      rw [F.map_target, G.map_target, ih]
    | comp k x y hx hy hm ihx ihy =>
      have hc : P.category.target k (Quotient.mk _ ⟨x, hx⟩) =
          P.category.source k (Quotient.mk _ ⟨y, hy⟩) := Quotient.sound hm
      rw [← P.mk_comp k ⟨x, hx⟩ ⟨y, hy⟩ hm hc]
      change F.map (P.category.comp k _ _ hc) = G.map (P.category.comp k _ _ hc)
      rw [F.map_comp k _ _ hc (F.map_composable hc), G.map_comp k _ _ hc (G.map_composable hc)]
      congr 1

end Thomason.OmegaCategory.Presentation

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

@[simp] lemma evaluate_generator (P : Presentation.{u}) (C : OmegaCategory.{u})
    (I : P.Interpretation C) (g : P.Generator) : P.evaluate C I (P.generator g) = I.map g := rfl

end Thomason.OmegaCategory.Presentation

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

variable {J : Type u} [Category.{u} J]


end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


lemma truncation_isTruncated (n : ℕ) (C : OmegaCategory.{u}) :
    (truncationPresentation n C).category.IsTruncated n := by
  intro x
  apply (truncationPresentation n C).cells_ext
  intro D I
  rw [Presentation.evaluate_source]
  exact I.satisfies.1 _


@[simp] lemma truncationLift_generator {n : ℕ} {C : OmegaCategory.{u}}
    (D : NCategory.{u} n) (F : Functor C D.val) (x : C.Cell) :
    (truncationLift D F).map ((truncationUnit n C).map x) = F.map x := rfl

lemma truncation_functor_ext {n : ℕ} {C D : OmegaCategory.{u}}
    {F G : Functor (truncation n C).val D}
    (h : Functor.comp (truncationUnit n C) F = Functor.comp (truncationUnit n C) G) : F = G := by
  apply (truncationPresentation n C).functor_ext
  intro x
  exact congrArg (fun H : Functor C D => H.map x) h

open CategoryTheory


noncomputable instance truncation_preservesColimits (n : ℕ) :
    Limits.PreservesColimitsOfSize.{v,w} (truncationFunctor.{u} n) :=
  (truncationAdjunction n).leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


@[simp] lemma uliftUp_down (C : OmegaCategory.{u}) :
    Functor.comp (uliftUp.{u,v} C) (uliftDown C) = Functor.id C := rfl

@[simp] lemma uliftDown_up (C : OmegaCategory.{u}) :
    Functor.comp (uliftDown.{u,v} C) (uliftUp C) = Functor.id (ulift C) := rfl

open CategoryTheory


end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite


end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite


noncomputable instance raisedOrientals_hasLeftKan :
    SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension raisedOrientals.{u} := by
  change (uliftYoneda.{u} : SimplexCategory ⥤ (SimplexCategoryᵒᵖ ⥤ Type u)).HasPointwiseLeftKanExtension raisedOrientals
  infer_instance


noncomputable instance categorification_preservesColimits :
    Limits.PreservesColimitsOfSize.{v,w} categorification.{u} :=
  categorificationAdjunction.leftAdjoint_preservesColimits

noncomputable instance categorificationFinite_preservesColimits (n : ℕ) :
    Limits.PreservesColimitsOfSize.{v,w} (categorificationFinite.{u} n) :=
  (categorificationFiniteAdjunction n).leftAdjoint_preservesColimits

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

instance nCategoryInclusion_full (n : ℕ) : (nCategoryInclusion.{u} n).Full where
  map_surjective f := ⟨f, rfl⟩

instance nCategoryInclusion_faithful (n : ℕ) : (nCategoryInclusion.{u} n).Faithful where
  map_injective h := h

noncomputable instance nCategoryInclusion_reflective (n : ℕ) :
    Reflective (nCategoryInclusion.{u} n) where
  L := truncationFunctor n
  adj := truncationAdjunction n

noncomputable instance nCategory_hasColimits (n : ℕ) : HasColimitsOfSize.{u,u} (NCategory.{u} n) :=
  hasColimits_of_reflective (nCategoryInclusion n)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory


end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped Topology Topology.Homotopy

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]


lemma loopMap_homotopic (N : Type w) (f : C(X, Y)) (x : X)
    {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (loopMap N f x p) (loopMap N f x q) :=
  h.comp_continuousMap f


end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory


noncomputable def thomasonFibrations : MorphismProperty OmegaCategory.{u} :=
  simplicialFibrations.inverseImage thomasonRight

noncomputable def thomasonCofibrations : MorphismProperty OmegaCategory.{u} :=
  (thomasonFibrations ⊓ thomasonWeakEquivalences).llp


noncomputable def thomasonFibrationsFinite (n : ℕ) :
    MorphismProperty (OmegaCategory.NCategory.{u} n) :=
  simplicialFibrations.inverseImage (thomasonRightFinite n)

noncomputable def thomasonCofibrationsFinite (n : ℕ) :
    MorphismProperty (OmegaCategory.NCategory.{u} n) :=
  (thomasonFibrationsFinite n ⊓ thomasonWeakEquivalencesFinite n).llp

end Thomason

end

end OAI
