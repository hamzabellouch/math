import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalSets

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
lemma widthLists_map (f : V→W) (fs : List V) (w : ℕ) :
    widthLists (fs.map f) w=(widthLists fs w).map (Finset.image f) := by
  induction w with
  | zero=>simp only [widthLists,List.map_cons,List.map_nil,Finset.image_empty]
  | succ w ih=>
    simp only [widthLists,ih,List.map_append,List.flatMap_map,List.map_flatMap,List.map_map]
    congr 1
    apply congrArg (fun g=>fs.flatMap g)
    funext i
    apply List.map_congr_left
    intro S _
    exact (Finset.image_insert f i S).symm
lemma exchangeList_map (f : V→W) (hf : Function.Injective f) (fs : List V) (S : Finset V) (w : ℕ) :
    exchangeList (fs.map f) (S.image f) w=(exchangeList fs S w).map (Finset.image f) := by
  simp only [exchangeList,widthLists_map,List.flatMap_map,List.map_map,Function.comp_def]
  have he : (widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>(S.image f \ R.image f) ∪ A.image f))=
      (widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>((S\R) ∪ A).image f)) := by
    apply congrArg (fun g=>(widthLists fs w).flatMap g)
    funext R
    apply List.map_congr_left
    intro A _
    rw [Finset.image_union,Finset.image_sdiff S R hf]
  rw [he]
  have hm : (widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>((S\R) ∪ A).image f))=
      ((widthLists fs w).flatMap (fun R=>(widthLists fs w).map (fun A=>(S\R) ∪ A))).map (Finset.image f) := by
    simp only [List.map_flatMap,List.map_map,Function.comp_def]
  rw [hm,List.filter_map]
  simp only [Function.comp_def,Finset.card_image_of_injective _ hf]
omit [DecidableEq V] [DecidableEq W] in
lemma listBest_map (f : V→W) (r : V→ℕ) (s : W→ℕ) (h : ∀ a,s (f a)=r a)
    (a : V) (xs : List V) : listBest s (f a) (xs.map f)=f (listBest r a xs) := by
  induction xs generalizing a with
  | nil=>rfl
  | cons b xs ih=>
    simp only [List.map_cons,listBest,h]
    split_ifs <;> exact ih _
lemma executableStep_map (f : V→W) (hf : Function.Injective f) (fs : List V)
    (r : Finset V→ℕ) (s : Finset W→ℕ) (h : ∀ T,s (T.image f)=r T) (S : Finset V) (w : ℕ) :
    executableStep (fs.map f) s w (S.image f)=(executableStep fs r w S).image f := by
  rw [executableStep,exchangeList_map f hf]
  exact listBest_map (Finset.image f) r s h S _
lemma executableDescent_map (f : V→W) (hf : Function.Injective f) (fs : List V)
    (r : Finset V→ℕ) (s : Finset W→ℕ) (h : ∀ T,s (T.image f)=r T) (S : Finset V) (w n : ℕ) :
    executableDescent (fs.map f) s w n (S.image f)=(executableDescent fs r w n S).image f := by
  induction n generalizing S with
  | zero=>rfl
  | succ n ih=>rw [executableDescent,executableStep_map f hf fs r s h,ih]; rfl
end MetricKMedianRecovery.LocalSearch

end OAI
