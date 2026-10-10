import OAI.CategoryTheory.Globular.CriticalJoint

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace TwoEndpoints
variable {K : Type u} [Category.{v} K] [HasPushouts K]
theorem base_property (W : MorphismProperty K) [W.IsStableUnderCobaseChange]
    [W.IsStableUnderComposition] {Bd Disk B : K} (i : Bd ⟶ Disk)
    (e : Bool → (Bd ⟶ B)) (hi : W i) : W (base i e) :=
  W.comp_mem _ _ (MorphismProperty.of_isPushout (IsPushout.of_hasPushout (e false) i) hi)
    (MorphismProperty.of_isPushout (IsPushout.of_hasPushout (e true ≫ pushout.inl (e false) i) i) hi)
end TwoEndpoints
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K] {D B : GlobularFrame K}
theorem oneSided_split_of_endpoint (e : Hom D B) (j : ℕ) [Epi (e.bd j)]
    (r : B.obj j ⟶ D.obj j) (hr : e.obj j ≫ r = 𝟙 _) :
    ∃ s : B.obj j ⟶ oneSided e j, oneSidedMap e j ≫ s = 𝟙 _ := by
  refine ⟨r ≫ pushout.inr (e.bd j) (D.inc j), ?_⟩
  apply pushout.hom_ext
  · apply (cancel_epi (e.bd j)).1
    erw [← Category.assoc _ (pushout.inl _ _), pushout.condition, Category.assoc,
      ← Category.assoc (pushout.inr _ _), pushout.inr_desc]
    erw [← Category.assoc (e.obj j) r, hr, Category.id_comp, Category.comp_id]
    exact pushout.condition.symm
  · erw [← Category.assoc, pushout.inr_desc, ← Category.assoc, hr, Category.id_comp,
      Category.comp_id]
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]

theorem cylinder_critical_joint_contractible (hnq : n ≤ q)
    (H : ExpansionContraction hC q (n+1)) :
    (GlobularFrame.jointSource (cylinderEndpoint hC q n) n).obj.underlying.HasFillers := by
  have hb : (cylinderEndpoint hC q n false).bd n = (cylinderEndpoint hC q n true).bd n := by
    change (cylinderNode hC q n n).bdEnd false = (cylinderNode hC q n n).bdEnd true
    rw [cylinderNode_critical]; rfl
  have : Epi ((cylinderEndpoint hC q n false).bd n) := by
    change Epi ((cylinderNode hC q n n).bdEnd false)
    rw [cylinderNode_critical]
    change Epi (𝟙 _); infer_instance
  obtain ⟨f,g,hfg⟩ := GlobularFrame.criticalJoint_retract (cylinderEndpoint hC q n) n
    (cylinderCriticalData hC q n false).iso
    (cylinderCriticalData hC q n false).endpoint
    (cylinderCriticalData hC q n true).endpoint hb
  exact ((cylinder_oneSided_contractible hC q n hnq H (n+1) (by omega) false).2.1).retract
    (underlyingMap f.hom) (underlyingMap g.hom)
    (congrArg (fun z : GlobularFrame.jointSource (cylinderEndpoint hC q n) n ⟶
      GlobularFrame.jointSource (cylinderEndpoint hC q n) n => underlyingMap z.hom) hfg)

theorem cylinder_joint_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (k : ℕ) (hk : n ≤ k) :
    (GlobularFrame.jointSource (cylinderEndpoint hC q n) k).obj.underlying.HasFillers := by
  by_cases he : k = n
  · subst k; exact cylinder_critical_joint_contractible hC q n hnq H
  · let f := TwoEndpoints.base ((cutoffDiskFrame hC q).diagram.source k)
      (fun ε => (cylinderEndpoint hC q n ε).obj k)
    have hf : (sourceClass hC q (n+1)).rlp.llp f := by
      apply TwoEndpoints.base_property
      rw [cutoffDiskFrame_source]
      intro X Y p hp
      exact hp _ (MorphismProperty.ofHoms.mk (⟨k,by omega⟩ : {j : ℕ // n+1 ≤ j}))
    exact H f hf (cylinderNode_contractible hC q n hnq H k).1
      (cylinderNode_contractible hC q n hnq H k).2

theorem cylinder_joint_split (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (k : ℕ) (hk : n ≤ k) :
    ∃ s : (cylinderFrame hC q n).obj (k+1) ⟶
        GlobularFrame.jointSource (cylinderEndpoint hC q n) k,
      GlobularFrame.jointSourceMap (cylinderEndpoint hC q n) k ≫ s = 𝟙 _ :=
  boundary_cofibration_split hC q _ (cylinderFrame_jointSource_upper hC q n k hk)
    (cylinder_joint_contractible hC q n hnq H k hk)

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
@[simp] theorem target_comp_unitMap (j : ℕ) : targetDisk C j ≫ unitMap C hC j = 𝟙 _ := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro f
  change C.Hom S.unop.shape (Shape.globe j) at f
  change C.comp (C.comp f (C.base (Shape.target j))) (C.unit hC j) = f
  rw [C.assoc, C.unit_target, C.comp_id]

theorem cylinder_oneSided_split (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (j : ℕ) (ε : Bool) :
    ∃ s : (cylinderFrame hC q n).obj j ⟶ GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j,
      GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j ≫ s = 𝟙 _ := by
  by_cases hj : n < j
  · exact cylinder_oneSided_split_high hC q n hnq H hj ε
  · have hepi : Epi ((cylinderEndpoint hC q n ε).bd j) := by
      change Epi ((cylinderNode hC q n j).bdEnd ε)
      by_cases he : j = n
      · subst j; rw [cylinderNode_critical]; change Epi (𝟙 _); infer_instance
      · rw [cylinderNode_low hC q n (by omega)]; change Epi (𝟙 _); infer_instance
    suffices hr : ∃ r : (cylinderFrame hC q n).obj j ⟶ (cutoffDiskFrame hC q).obj j,
        (cylinderEndpoint hC q n ε).obj j ≫ r = 𝟙 _ by
      obtain ⟨r,hr⟩ := hr
      exact GlobularFrame.oneSided_split_of_endpoint (cylinderEndpoint hC q n ε) j r hr
    change ∃ r : (cylinderNode hC q n j).obj ⟶ (cutoffDiskFrame hC q).obj j,
      (cylinderNode hC q n j).endpoint ε ≫ r = 𝟙 _
    by_cases he : j = n
    · subst j
      rw [cylinderNode_critical]
      refine ⟨(cutoffFunctor hC q).map (unitMap C hC n), ?_⟩
      cases ε
      · change (cutoffDiskFrame hC q).diagram.source n ≫ _ = _
        rw [cutoffDiskFrame_source]
        change (cutoffFunctor hC q).map (J C n) ≫ _ = _
        erw [← Functor.map_comp, J_comp_unitMap]
        exact (cutoffFunctor hC q).map_id _
      · change (cutoffDiskFrame hC q).diagram.target n ≫ _ = _
        erw [cutoffDiskFrame_target, ← Functor.map_comp, target_comp_unitMap]
        exact (cutoffFunctor hC q).map_id _
    · rw [cylinderNode_low hC q n (by omega)]
      exact ⟨𝟙 _, Category.id_comp _⟩
end GlobularTheory.Model
end Grothendieck

end OAI
