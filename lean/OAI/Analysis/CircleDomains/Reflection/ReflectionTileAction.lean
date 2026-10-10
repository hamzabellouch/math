import OAI.Analysis.CircleDomains.Reflection.ReflectionTiles

namespace OAI

/-! The exact action of a generating reflection on reduced words and their
geometric tiles, including cancellation of the leading generator. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity
variable {X I : Type*} [TopologicalSpace X] [DecidableEq I]

def reflectionReduceStep (i : I) : List I → List I
  | [] => [i]
  | j::w => if i=j then w else i::j::w

lemma reflectionReduceStep_isChain (i : I) (w : List I) (hw : w.IsChain (·≠·)) :
    (reflectionReduceStep i w).IsChain (·≠·) := by
  cases w with
  | nil => simp [reflectionReduceStep]
  | cons j w =>
    by_cases hij : i=j
    · simpa only [reflectionReduceStep,ite_eq_left hij] using (List.isChain_cons.mp hw).2
    · simpa only [reflectionReduceStep,ite_eq_right hij,List.isChain_cons_cons] using And.intro hij hw

lemma reflectionReduceStep_involutive (i : I) (w : List I) (hw : w.IsChain (·≠·)) :
    reflectionReduceStep i (reflectionReduceStep i w)=w := by
  cases w with
  | nil => simp [reflectionReduceStep]
  | cons j w =>
    by_cases hij : i=j
    · subst j
      cases w with
      | nil => simp [reflectionReduceStep]
      | cons k w =>
        have hik := (List.isChain_cons_cons.mp hw).1
        simp [reflectionReduceStep,hik]
    · simp [reflectionReduceStep,hij]

lemma reflectionWord_reduceStep (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i))
    (i : I) (w : List I) (x : X) :
    reflectionWord R (reflectionReduceStep i w) x=R i (reflectionWord R w x) := by
  cases w with
  | nil => rfl
  | cons j w =>
    by_cases hij : i=j
    · subst j
      simp only [reflectionReduceStep,ite_true,reflectionWord,Homeomorph.trans_apply]
      exact (hR i _).symm
    · simp only [reflectionReduceStep,ite_eq_right hij,reflectionWord,Homeomorph.trans_apply]

lemma reflectionTile_reduceStep (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i))
    (K : I → Set X) (i : I) (w : List I) :
    reflectionTile R K (reflectionReduceStep i w)=R i '' reflectionTile R K w := by
  unfold reflectionTile
  rw [image_image]
  exact image_congr (fun x _ => reflectionWord_reduceStep R hR i w x)

lemma reflection_tiles_union_invariant (R : I → X ≃ₜ X) (hR : ∀i,Involutive (R i))
    (K : I → Set X) (i : I) :
    R i '' (⋃w : {w : List I // w.IsChain (·≠·)},reflectionTile R K w.val)=
      ⋃w : {w : List I // w.IsChain (·≠·)},reflectionTile R K w.val := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨w,hw⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨⟨reflectionReduceStep i w.val,reflectionReduceStep_isChain i w.val w.property⟩,?_⟩
    rw [reflectionTile_reduceStep R hR]
    exact mem_image_of_mem (R i) hw
  · intro x hx
    obtain ⟨w,hw⟩ := mem_iUnion.mp hx
    refine ⟨R i x,?_,hR i x⟩
    refine mem_iUnion.mpr ⟨⟨reflectionReduceStep i w.val,reflectionReduceStep_isChain i w.val w.property⟩,?_⟩
    rw [reflectionTile_reduceStep R hR]
    exact mem_image_of_mem (R i) hw

end CircleDomainRigidity

end

end OAI
