import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PiFiber

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet
open FreeChains

variable {n:ℕ} (X:Fin n→SSet) (x:∀i,(X i).obj (op ⦋0⦌))
noncomputable def h1Cocone : Cofan (fun i=>(X i).homology Z 1) :=
  Cofan.mk ((obj X).homology Z 1) (fun i=>SSet.homologyMap (incl X x i) Z 1)
lemma incl_proj_h1 (i j:Fin n) :
    SSet.homologyMap (incl X x i) Z 1 ≫ SSet.homologyMap (proj X j) Z 1=
      if h:i=j then eqToHom (congrArg (fun i=>(X i).homology Z 1) h) else 0 := by
  classical
  rw [←SSet.homologyMap_comp]
  by_cases h:i=j
  · subst j; simp
  · rw [incl_other X x h,ConnectedProduct.const_homology_zero _ 1 (by decide)]
    simp [h]
lemma h1_decomposition (hX:∀i,(X i).IsConnected) :
    ∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ SSet.homologyMap (incl X x i) Z 1=𝟙 _ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply homology_ext n X hX
  intro j
  change ((∑ i:Fin n, SSet.homologyMap (proj X i) Z 1 ≫ SSet.homologyMap (incl X x i) Z 1) ≫
      SSet.homologyMap (proj X j) Z 1) a=SSet.homologyMap (proj X j) Z 1 a
  rw [Preadditive.sum_comp]
  simp_rw [Category.assoc]
  rw [Finset.sum_eq_single j]
  · rw [incl_proj_h1]; simp
  · intro i hi hij; rw [incl_proj_h1]; simp [hij]
  · simp
noncomputable def h1IsColimit (hX:∀i,(X i).IsConnected) : IsColimit (h1Cocone X x) where
  desc s := ∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ s.ι.app ⟨i⟩
  fac s j := by
    classical
    cases j with | mk j =>
      change SSet.homologyMap (incl X x j) Z 1 ≫
        (∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ s.ι.app ⟨i⟩)=s.ι.app ⟨j⟩
      rw [Preadditive.comp_sum,Finset.sum_eq_single j]
      · rw [←Category.assoc,incl_proj_h1]; simp
      · intro i hi hij; rw [←Category.assoc,incl_proj_h1]; simp [Ne.symm hij]
      · simp
  uniq s f hf := by
    dsimp only [h1Cocone, Cofan.mk_pt] at f hf ⊢
    change f = ∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ s.ι.app ⟨i⟩
    rw [←Category.id_comp f,←h1_decomposition X x hX,Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Category.assoc]
    exact congrArg (fun g=>SSet.homologyMap (proj X i) Z 1 ≫ g) (hf ⟨i⟩)
end PiSSet

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def evalIso (n:ℕ) :
    (nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 ≅
      (PiFiber.prod C (Fin n)).homology Z 1 := by
  haveI := NerveHomotopy.homologyMap_isIso (IntervalBar.Diagram.eval (C:=C) n) Z 1
  exact asIso (SSet.homologyMap (nerveMap (IntervalBar.Diagram.eval (C:=C) n)) Z 1) ≪≫
    (SSet.homologyFunctor Z 1).mapIso (PiSSet.nervePiIso (fun _:Fin n=>C))
noncomputable def points {n:ℕ} (p:Fin n→Skeleton C) :
    ∀i,(nerve (Fiber (p i))).obj (op ⦋0⦌) := fun i=>nerveEquiv.symm (base (p i))
noncomputable def primitive {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    (nerve (Fiber (p i))).homology Z 1 ⟶
      (nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 :=
  SSet.homologyMap (PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i) Z 1 ≫
    SSet.homologyMap (PiFiber.inclusion C (Fin n) p) Z 1 ≫ (evalIso n).inv
omit [SymmetricCategory C] in
lemma hom_ext {n:ℕ} {M:A}
    {f g:(nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 ⟶ M}
    (h:∀ (p:Fin n→Skeleton C) (i:Fin n),primitive p i ≫ f=primitive p i ≫ g) : f=g := by
  apply (cancel_epi (evalIso n).inv).mp
  apply (PiFiber.homologyIsColimit C (Fin n) 1).hom_ext
  intro p
  apply (PiSSet.h1IsColimit (fun i=>nerve (Fiber (p.as i))) (points p.as) (fun _=>inferInstance)).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans ((h p.as i.as).trans (Category.assoc _ _ _))
noncomputable def descCocone {n:ℕ} {M:A}
    (f:∀ (p:Fin n→Skeleton C) (i:Fin n),(nerve (Fiber (p i))).homology Z 1 ⟶ M) :
    Cocone (PiFiber.diagram C (Fin n) ⋙ SSet.homologyFunctor Z 1) where
  pt := M
  ι := Discrete.natTrans (fun p => (PiSSet.h1IsColimit (fun i=>nerve (Fiber (p.as i))) (points p.as) (fun _=>inferInstance)).desc
      (Cofan.mk M (f p.as)))
noncomputable def desc {n:ℕ} {M:A}
    (f:∀ (p:Fin n→Skeleton C) (i:Fin n),(nerve (Fiber (p i))).homology Z 1 ⟶ M) :
    (nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 ⟶ M :=
  (evalIso n).hom ≫ (PiFiber.homologyIsColimit C (Fin n) 1).desc (descCocone f)
omit [SymmetricCategory C] in
@[reassoc (attr:=simp)] lemma primitive_desc {n:ℕ} {M:A}
    (f:∀ (p:Fin n→Skeleton C) (i:Fin n),(nerve (Fiber (p i))).homology Z 1 ⟶ M)
    (p:Fin n→Skeleton C) (i:Fin n) : primitive p i ≫ desc f=f p i := by
  let coordinateMap : (nerve (Fiber (p i))).homology Z 1 ⟶
      (PiFiber.piece C (Fin n) p).homology Z 1 :=
    SSet.homologyMap (PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i) Z 1
  let inclusionMap : (PiFiber.piece C (Fin n) p).homology Z 1 ⟶
      (PiFiber.prod C (Fin n)).homology Z 1 :=
    SSet.homologyMap (PiFiber.inclusion C (Fin n) p) Z 1
  let coconeDesc : (PiFiber.prod C (Fin n)).homology Z 1 ⟶ M :=
    (PiFiber.homologyIsColimit C (Fin n) 1).desc (descCocone f)
  change (coordinateMap ≫ inclusionMap ≫ (evalIso n).inv) ≫
    (evalIso n).hom ≫ coconeDesc = f p i
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have h:=(PiFiber.homologyIsColimit C (Fin n) 1).fac (descCocone f) ⟨p⟩
  change inclusionMap ≫ coconeDesc = _ at h
  rw [h]
  exact (PiSSet.h1IsColimit (fun j=>nerve (Fiber (p j))) (points p) (fun _=>inferInstance)).fac
    (Cofan.mk M (f p)) ⟨i⟩
end MarkedH1

end

end OAI
