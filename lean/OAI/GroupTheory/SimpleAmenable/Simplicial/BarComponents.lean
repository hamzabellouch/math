import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.BarRowFiniteness

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

section
open NerveComponents FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma single_eqToHom {P:Type} [Monoid P] {x y:SingleObj P} (h:x=y) : eqToHom h=(1:P) := by subst y; rfl
noncomputable def componentSimplex {n:ℕ} (D:Diagram C (Fin (n+1))) :
    ComposableArrows (SingleObj (Skeleton C)) n where
  obj _ := SingleObj.star _
  map {i j} f := toSkeleton (D.obj i j (leOfHom f))
  map_id i := congr_toSkeleton_of_iso (D.unit i)
  map_comp {i j k} f g := by
    change toSkeleton (D.obj i k _) = toSkeleton (D.obj j k _) * toSkeleton (D.obj i j _)
    rw [mul_comm,←Skeleton.toSkeleton_tensorObj]
    exact (congr_toSkeleton_of_iso (D.cut i j k (leOfHom f) (leOfHom g))).symm
lemma componentSimplex_iso {n:ℕ} {D E:Diagram C (Fin (n+1))} (e:D≅E) :
    componentSimplex D=componentSimplex E := by
  apply ComposableArrows.ext (F:=componentSimplex D) (G:=componentSimplex E) (fun _=>rfl)
  intro i hi
  simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]
  exact congr_toSkeleton_of_iso (asIso (e.hom.app _ _ _))
noncomputable def skeletonSimplex (n:ℕ) : Skeleton (Diagram C (Fin (n+1))) →
    ComposableArrows (SingleObj (Skeleton C)) n :=
  Quotient.lift componentSimplex (by rintro D E ⟨e⟩; exact componentSimplex_iso e)
@[simp] lemma skeletonSimplex_mk {n:ℕ} (D:Diagram C (Fin (n+1))) :
    skeletonSimplex n (toSkeleton D)=componentSimplex D := rfl
lemma componentSimplex_reindex {n m:ℕ} (u:⦋m⦌⟶⦋n⦌) (D:Diagram C (Fin (n+1))) :
    componentSimplex ((reindex u.toOrderHom).obj D)=
      (nerve (SingleObj (Skeleton C))).map u.op (componentSimplex D) := rfl
lemma skeletonSimplex_natural {n m:ℕ} (u:⦋m⦌⟶⦋n⦌) (p:Skeleton (Diagram C (Fin (n+1)))) :
    skeletonSimplex m (NerveComponents.map (reindex u.toOrderHom) p)=
      (nerve (SingleObj (Skeleton C))).map u.op (skeletonSimplex n p) := by
  obtain ⟨D,rfl⟩ := Quotient.exists_rep p
  rfl
lemma skeletonSimplex_injective (n:ℕ) : Function.Injective (skeletonSimplex (C:=C) n) := by
  intro D E h
  obtain ⟨D,rfl⟩ := Quotient.exists_rep D
  obtain ⟨E,rfl⟩ := Quotient.exists_rep E
  apply congr_toSkeleton_of_iso
  apply (eval n).preimageIso
  refine { hom := fun i=>?_,inv:=fun i=>?_,hom_inv_id:=?_,inv_hom_id:=?_ }
  · exact (Skeleton.isoOfEq (congrArg (fun s:ComposableArrows (SingleObj (Skeleton C)) n=>
      s.map (homOfLE (Fin.castSucc_le_succ i))) h)).hom
  · exact (Skeleton.isoOfEq (congrArg (fun s:ComposableArrows (SingleObj (Skeleton C)) n=>
      s.map (homOfLE (Fin.castSucc_le_succ i))) h)).inv
  · funext i; exact Iso.hom_inv_id _
  · funext i; exact Iso.inv_hom_id _
lemma skeletonSimplex_surjective (n:ℕ) : Function.Surjective (skeletonSimplex (C:=C) n) := by
  intro s
  let U : Fin n → C := fun i=>(fromSkeleton C).obj (s.map (homOfLE (Fin.castSucc_le_succ i)))
  refine ⟨toSkeleton ((eval n).objPreimage U),?_⟩
  apply ComposableArrows.ext (fun _=>Subsingleton.elim _ _)
  intro i hi
  have e := ((eval n).objObjPreimageIso U)
  simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]
  exact (congr_toSkeleton_of_iso (asIso (e.hom ⟨i,hi⟩))).trans (toSkeleton_fromSkeleton_obj _)
noncomputable def skeletonSimplexEquiv (n:ℕ) : Skeleton (Diagram C (Fin (n+1))) ≃
    ComposableArrows (SingleObj (Skeleton C)) n :=
  Equiv.ofBijective (skeletonSimplex n) ⟨skeletonSimplex_injective n,skeletonSimplex_surjective n⟩
noncomputable def componentsZeroIso (n:ℕ) :
    (nerve (Diagram C (Fin (n+1)))).homology Z 0 ≅
      (ModuleCat.free ℤ).obj ((nerve (SingleObj (Skeleton C))).obj (op ⦋n⦌)) :=
  NerveComponents.zeroIso ≪≫ (ModuleCat.free ℤ).mapIso (skeletonSimplexEquiv n).toIso
end

open NerveComponents FreeChains AlgebraicTopology

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma componentsZeroIso_natural {n m:ℕ} (u:⦋m⦌⟶⦋n⦌) :
    SSet.homologyMap (nerveMap (reindex (C:=C) u.toOrderHom)) Z 0 ≫ (componentsZeroIso m).hom =
      (componentsZeroIso n).hom ≫ (ModuleCat.free ℤ).map ((nerve (SingleObj (Skeleton C))).map u.op) := by
  change SSet.homologyMap (nerveMap (reindex (C:=C) u.toOrderHom)) Z 0 ≫
      ((zeroIso (C:=Diagram C (Fin (m+1)))).hom ≫
        (ModuleCat.free ℤ).map (skeletonSimplexEquiv m).toIso.hom) =
    ((zeroIso (C:=Diagram C (Fin (n+1)))).hom ≫
      (ModuleCat.free ℤ).map (skeletonSimplexEquiv n).toIso.hom) ≫
        (ModuleCat.free ℤ).map ((nerve (SingleObj (Skeleton C))).map u.op)
  rw [←Category.assoc,NerveComponents.zeroIso_natural,Category.assoc,←Functor.map_comp,
    Category.assoc]
  erw [←Functor.map_comp]
  congr 2
  apply ConcreteCategory.hom_ext
  intro p
  exact skeletonSimplex_natural u p
noncomputable def componentRowIso :
    simplicial (C:=C) ⋙ nerveFunctor ⋙ SSet.homologyFunctor Z 0 ≅
      nerve (SingleObj (Skeleton C)) ⋙ ModuleCat.free ℤ :=
  NatIso.ofComponents (fun p=>componentsZeroIso p.unop.len) (fun {_ _} u=>componentsZeroIso_natural u.unop)
noncomputable def componentRowChainIso :
    AlternatingFaceMapComplex.obj (simplicial (C:=C) ⋙ nerveFunctor ⋙ SSet.homologyFunctor Z 0) ≅
      FreeChains.complex (nerve (SingleObj (Skeleton C))) :=
  (alternatingFaceMapComplex A).mapIso componentRowIso
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace FilteredNerve
open FreeChains

variable (C:Type) [Category.{0} C]
def diagram : C ⥤ SSet := Over.mapFunctor C ⋙ nerveFunctor
def cocone : Cocone (diagram C) where
  pt := nerve C
  ι := { app x := nerveMap (Over.forget x)
         naturality x y f := by change nerveMap (Over.map f ⋙ Over.forget y)=_; rfl }
def lastCocone {n:ℕ} (s:ComposableArrows C n) : s ⟶ (Functor.const _).obj s.right where
  app i := s.map (homOfLE (Fin.le_last i))
  naturality i j f := by
    change s.map f ≫ s.map (homOfLE (Fin.le_last j)) = s.map (homOfLE (Fin.le_last i)) ≫ 𝟙 _
    rw [Category.comp_id,←s.map_comp]
    congr 1
def lift {n:ℕ} (s:ComposableArrows C n) : ComposableArrows (Over s.right) n :=
  Over.lift s (lastCocone C s)
lemma lift_forget {n:ℕ} (s:ComposableArrows C n) : lift C s ⋙ Over.forget s.right=s := rfl
lemma lift_map {n:ℕ} {x:C} (s:ComposableArrows (Over x) n) :
    lift C (s ⋙ Over.forget x) ⋙ Over.map s.right.hom=s := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    refine Comma.ext (x:=(lift C (s ⋙ Over.forget x) ⋙ Over.map s.right.hom).obj i)
      (y:=s.obj i) rfl (Subsingleton.elim _ _) ?_
    apply heq_of_eq
    change (s.map (homOfLE (Fin.le_last i))).left ≫ s.right.hom=(s.obj i).hom
    exact (s.map (homOfLE (Fin.le_last i))).w
  case h_map =>
    intro i j f
    apply Over.OverMorphism.ext
    simp only [Functor.comp_map,Over.comp_left]
    erw [Over.eqToHom_left,Over.eqToHom_left]
    simp [lift,Over.lift]
    erw [eqToHom_refl,Category.id_comp]
noncomputable def pointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C)) where
  desc d := ↾fun s => d.ι.app s.right (lift C s)
  fac d x := by
    ext s
    have h:=congrArg (fun k => k (lift C (s ⋙ Over.forget x))) (d.w s.right.hom)
    change d.ι.app x (lift C (s ⋙ Over.forget x) ⋙ Over.map s.right.hom)=_ at h
    erw [lift_map] at h
    exact h.symm
  uniq d m hm := by
    ext s
    have h:=congrArg (fun k => k (lift C s)) (hm s.right)
    exact h
noncomputable def isColimit : IsColimit (cocone C) :=
  evaluationJointlyReflectsColimits _ (fun n => pointwiseIsColimit C n.unop.len)
lemma terminal_acyclic {D:Type} [Category.{0} D] (d:D) (hd:IsTerminal d)
    (n:ℕ) (hn:n≠0) : IsZero ((nerve D).homology Z n) := by
  let α : 𝟭 D ⟶ (Functor.const D).obj d :=
    { app x := hd.from x
      naturality x y f := hd.hom_ext _ _ }
  have h := (NerveHomotopy.ofNatTrans α).congr_homologyMap Z n
  change SSet.homologyMap (𝟙 (nerve D)) Z n = SSet.homologyMap (nerveMap ((Functor.const D).obj d)) Z n at h
  rw [SSet.homologyMap_id,CategoryTheory.nerve.const_map] at h
  erw [ConnectedProduct.const_homology_zero _ n hn] at h
  exact (IsZero.iff_id_eq_zero _).mpr h
instance connected [IsFiltered C] : (nerve C).IsConnected where
  allEq u v := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective v
    let a := nerveEquiv x
    let b := nerveEquiv y
    have h₁ := SSet.π₀.sound (nerve.edgeMk (IsFiltered.leftToMax a b))
    have h₂ := SSet.π₀.sound (nerve.edgeMk (IsFiltered.rightToMax a b))
    have component_eq := h₁.trans h₂.symm
    change SSet.π₀.mk (X:=nerve C) (nerveEquiv.symm (nerveEquiv x)) =
      SSet.π₀.mk (X:=nerve C) (nerveEquiv.symm (nerveEquiv y)) at component_eq
    erw [Equiv.symm_apply_apply,Equiv.symm_apply_apply] at component_eq
    exact component_eq
  nonempty := by
    let := IsFiltered.nonempty (C:=C)
    exact ⟨nerveEquiv.symm (Classical.arbitrary C)⟩
lemma positive_acyclic [IsFiltered C] (n:ℕ) (hn:n≠0) : IsZero ((nerve C).homology Z n) := by
  let h:=isColimitOfPreserves (SSet.homologyFunctor Z n) (isColimit C)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply h.hom_ext
  intro x
  have hz : IsZero ((nerve (Over x)).homology Z n) :=
    terminal_acyclic (Over.mk (𝟙 x)) Over.mkIdTerminal n hn
  exact hz.eq_of_src _ _
end FilteredNerve

end OAI
