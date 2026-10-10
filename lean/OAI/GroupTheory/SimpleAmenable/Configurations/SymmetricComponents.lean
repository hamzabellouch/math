import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricStable
import OAI.GroupTheory.SimpleAmenable.Configurations.CofinalPowers
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonComponentStable
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarForwardLow

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
noncomputable abbrev generator : Skeleton FiniteSetGroupoid := toSkeleton ⟨1⟩
lemma component_pow (n:ℕ) : toSkeleton (⟨n⟩:FiniteSetGroupoid)=generator^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,←ih]
    exact Skeleton.toSkeleton_tensorObj (⟨n⟩:FiniteSetGroupoid) ⟨1⟩
lemma generator_surjective : Function.Surjective (fun n:ℕ=>generator^n) := by
  intro p
  exact ⟨(repr p).size,(component_pow _).symm.trans (repr_component p)⟩
lemma generator_cofinal : ∀p:Skeleton FiniteSetGroupoid,∃q n,p*q=generator^n := by
  intro p
  obtain ⟨n,rfl⟩:=generator_surjective p
  exact ⟨1,n,mul_one _⟩
noncomputable def standardNerveInclusion (n:ℕ) : SingleObj (G n) ⥤ FiniteSetGroupoid where
  obj _ := ⟨n⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
noncomputable def standardFiberInclusion (n:ℕ) : SingleObj (G n) ⥤ Fiber (generator^n) :=
  (property (generator^n)).lift (standardNerveInclusion n) (fun _=>component_pow n)
instance standardFiberInclusion_faithful (n:ℕ) : (standardFiberInclusion n).Faithful where
  map_injective h := congrArg (fun f : (standardFiberInclusion n).obj _ ⟶ (standardFiberInclusion n).obj _=>f.hom) h
noncomputable instance standardFiberInclusion_full (n:ℕ) : (standardFiberInclusion n).Full where
  map_surjective f := ⟨f.hom,rfl⟩
instance standardFiberInclusion_essSurj (n:ℕ) : (standardFiberInclusion n).EssSurj where
  mem_essImage V := ⟨SingleObj.star _,⟨fiberIso _ ((standardFiberInclusion n).obj (SingleObj.star _)) V⟩⟩
noncomputable instance standardFiberInclusion_isEquivalence (n:ℕ) : (standardFiberInclusion n).IsEquivalence :=
  ⟨inferInstance,inferInstance,inferInstance⟩
noncomputable def standardHomologyIso (n q:ℕ) :
    groupHomology (Rep.trivial ℤ (G n) ℤ) q ≅ (nerve (Fiber (generator^n))).homology Z q := by
  haveI:=NerveHomotopy.homologyMap_isIso (standardFiberInclusion n) Z q
  exact (GroupNerveCoordinates.homologyIso (G n) q).symm ≪≫
    asIso (SSet.homologyMap (nerveMap (standardFiberInclusion n)) Z q)
lemma tensor_stabilize (k n:ℕ) (f:G n) :
    (tensorLeft (⟨k⟩:FiniteSetGroupoid)).map (show (⟨n⟩:FiniteSetGroupoid) ⟶ ⟨n⟩ from f)=
      (show (⟨k+n⟩:FiniteSetGroupoid) ⟶ ⟨k+n⟩ from stabilize k n f) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩:=finSumFinEquiv.surjective x
  cases y with
  | inl i =>
    change FiniteSetGroupoid.sumHom (Equiv.refl (Fin k)) f (FiniteSetGroupoid.sumEquiv ⟨k⟩ ⟨n⟩ (.inl i))=stabilize k n f (Fin.castAdd n i)
    rw [FiniteSetGroupoid.sumHom_inl,stabilize_apply_head]
    rfl
  | inr i =>
    change FiniteSetGroupoid.sumHom (Equiv.refl (Fin k)) f (FiniteSetGroupoid.sumEquiv ⟨k⟩ ⟨n⟩ (.inr i))=stabilize k n f (Fin.natAdd k i)
    rw [FiniteSetGroupoid.sumHom_inr,stabilize_apply_tail]
    rfl
noncomputable def standardTensorIso (k n:ℕ) :
    standardNerveInclusion n ⋙ tensorLeft (⟨k⟩:FiniteSetGroupoid) ≅
      (stabilize k n).toFunctor ⋙ standardNerveInclusion (k+n) :=
  NatIso.ofComponents (fun _=>Iso.refl _) (by
    intro X Y f
    change FiniteSetGroupoid.sumHom (Equiv.refl (Fin k)) f = stabilize k n f
    exact tensor_stabilize k n f)
noncomputable def standardCastIso {m n:ℕ} (h:m=n) : standardNerveInclusion m ≅
    (castGroup h).toMonoidHom.toFunctor ⋙ standardNerveInclusion n := by
  subst n
  exact Iso.refl _
noncomputable def standardSuccessorIso (n:ℕ) :
    standardNerveInclusion n ⋙ tensorLeft (⟨1⟩:FiniteSetGroupoid) ≅
      (successorStabilize n).toFunctor ⋙ standardNerveInclusion (n+1) :=
  standardTensorIso 1 n ≪≫
    Functor.isoWhiskerLeft (stabilize 1 n).toFunctor (standardCastIso (Nat.add_comm 1 n)) ≪≫
      (Functor.associator _ _ _).symm
end SimpleAmenable.SymmetricConfiguration

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
noncomputable def representativeGeneratorIso : repr generator ≅ (⟨1⟩:FiniteSetGroupoid) :=
  Skeleton.isoOfEq (repr_component _)
noncomputable def representativeSuccessorIso (n:ℕ) :
    standardNerveInclusion n ⋙ tensorLeft (repr generator) ≅
      (successorStabilize n).toFunctor ⋙ standardNerveInclusion (n+1) :=
  Functor.isoWhiskerLeft (standardNerveInclusion n)
    ((tensoringLeft FiniteSetGroupoid).mapIso representativeGeneratorIso) ≪≫ standardSuccessorIso n
noncomputable def fiberSuccessorIso (n:ℕ) :
    standardFiberInclusion n ⋙
      ComponentTranslation.translate generator (generator^n) (generator^(n+1)) (pow_succ' _ _).symm ≅
        (successorStabilize n).toFunctor ⋙ standardFiberInclusion (n+1) :=
  NatIso.ofComponents (fun x=>ObjectProperty.isoMk _ ((representativeSuccessorIso n).app x)) (by
    intro x y f
    apply ObjectProperty.hom_ext
    exact (representativeSuccessorIso n).hom.naturality f)
lemma component_successor_isIso (n q:ℕ) [IsIso (TrivialHomology.map (successorStabilize n) q)] :
    IsIso (SSet.homologyMap (nerveMap
      (ComponentTranslation.translate generator (generator^n) (generator^(n+1)) (pow_succ' _ _).symm)) Z q) := by
  have := NerveHomotopy.homologyMap_isIso (standardFiberInclusion n) Z q
  have := NerveHomotopy.homologyMap_isIso (standardFiberInclusion (n+1)) Z q
  have hg:=GroupNerveCoordinates.homologyIso_natural (successorStabilize n) q
  have : IsIso (SSet.homologyMap (nerveMap (successorStabilize n).toFunctor) Z q) := by
    have : IsIso (SSet.homologyMap (nerveMap (successorStabilize n).toFunctor) Z q ≫
      (GroupNerveCoordinates.homologyIso (G (n+1)) q).hom) := by rw [hg]; infer_instance
    exact (isIso_comp_right_iff _ (GroupNerveCoordinates.homologyIso (G (n+1)) q).hom).mp inferInstance
  have h:=(NerveHomotopy.ofNatTrans (fiberSuccessorIso n).hom).congr_homologyMap Z q
  rw [ComponentStable.map_comp,ComponentStable.map_comp] at h
  have : IsIso (SSet.homologyMap (nerveMap (standardFiberInclusion n)) Z q ≫
    SSet.homologyMap (nerveMap
      (ComponentTranslation.translate generator (generator^n) (generator^(n+1)) (pow_succ' _ _).symm)) Z q) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff (SSet.homologyMap (nerveMap (standardFiberInclusion n)) Z q) _).mp inferInstance
lemma component_sequence_succ (n q:ℕ) :
    (homologyDiagram (C:=FiniteSetGroupoid) q).map
      ((CofinalPowers.sequence generator).map (homOfLE (Nat.le_succ n))) =
        SSet.homologyMap (nerveMap (ComponentTranslation.translate generator
          (generator^n) (generator^(n+1)) (pow_succ' _ _).symm)) Z q := by
  change SSet.homologyMap (nerveMap (ComponentTranslation.translate
    (generator ^ (n+1-n)) _ _ _)) Z q = _
  simp only [Nat.add_sub_cancel_left,pow_one]
  rfl
lemma componentStable_finite (q:ℕ) (N:ℕ)
    (h:∀n,N≤n → IsIso (TrivialHomology.map (successorStabilize n) q)) :
    Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) q:A) := by
  have := FiniteGroupHomology.finite (Rep.trivial ℤ (G N) ℤ) q
  have : Module.Finite ℤ ((nerve (Fiber (generator^N))).homology Z q:A) :=
    Module.Finite.equiv (standardHomologyIso N q).toLinearEquiv
  apply (CofinalPowers.finite_colimit_iff generator generator_cofinal (homologyDiagram q) N N le_rfl ?_).mp
    (inferInstanceAs (Module.Finite ℤ ((nerve (Fiber (generator^N))).homology Z q:A)))
  intro n hn
  rw [component_sequence_succ]
  have := h n hn
  exact component_successor_isIso n q
lemma componentStableH1_finite : Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) 1:A) :=
  componentStable_finite 1 32 successor_H1_isIso
lemma componentStableH2_finite : Module.Finite ℤ (ComponentStable.object (C:=FiniteSetGroupoid) 2:A) :=
  componentStable_finite 2 34 successor_H2_isIso
lemma component_fg : Monoid.FG (Skeleton FiniteSetGroupoid) :=
  Monoid.fg_of_surjective (powersHom (Skeleton FiniteSetGroupoid) generator) (by
    intro p
    obtain ⟨n,hn⟩:=generator_surjective p
    exact ⟨Multiplicative.ofAdd n,hn⟩)
lemma component_homology_finite (n:ℕ) :
    Module.Finite ℤ ((nerve (SingleObj (Skeleton FiniteSetGroupoid))).homology Z n:A) := by
  have := component_fg
  have : Group.FG (TranslationFiltered.Q (Skeleton FiniteSetGroupoid)) := Group.fg_iff_monoid_fg.mpr inferInstance
  have := AbelianHomologyFinite.finite (TranslationFiltered.Q (Skeleton FiniteSetGroupoid)) n
  exact Module.Finite.equiv (TranslationNerve.completionHomologyIso (Skeleton FiniteSetGroupoid) n).symm.toLinearEquiv
lemma triple_homology_finite (n:ℕ) (hn:n≤5) :
    Module.Finite ℤ ((IntervalBar.Diagram.bar₃ (C:=FiniteSetGroupoid)).homology Z n:A) := by
  have := componentStableH1_finite
  have := componentStableH2_finite
  exact IntervalBar.Diagram.triple_finite_of_bar
    (IntervalBar.Diagram.bar_low_finite component_homology_finite) n hn
end SimpleAmenable.SymmetricConfiguration

end

end OAI
