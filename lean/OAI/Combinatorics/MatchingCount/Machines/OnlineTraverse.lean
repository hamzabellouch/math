import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineFold
import OAI.Combinatorics.MatchingCount.Machines.OnlineFrame

namespace OAI

namespace MatchingFPRAS.OnlineTree
open PhysicalStream TreeTyped

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def traverseM (f : A → Experiment B) : List A → Experiment (List B)
  | [] => .done []
  | a::as => (f a).bind (fun b=>(traverseM f as).map (List.cons b))
def collectStep (f : A → Experiment B) (x : A×List B) : Experiment (List B) :=
  (f x.1).map (fun b=>b::x.2)
noncomputable def collectStepRealizer {f : A → Experiment B} (F : Realizer f) :
    Realizer (collectStep f) :=
  (composition (pair (composition (deterministic TreeTyped.first) F)
    (deterministic TreeTyped.second)) (deterministic TreeTyped.listCons)).congr (by
      intro x h; simp only [Experiment.mean_bind,Experiment.mean_map,Experiment.mean,collectStep])
omit [Codec A] [Codec B] in
lemma mean_fold_collect (f : A → Experiment B) (as : List A) (bs : List B) (h : List B → ℚ) :
    (foldM (collectStep f) as bs).mean h=(traverseM f as).mean (fun cs=>h (cs.reverse++bs)) := by
  induction as generalizing bs with
  | nil => simp only [foldM,traverseM,Experiment.mean,List.reverse_nil,List.nil_append]
  | cons a as ih =>
    simp only [foldM,traverseM,collectStep,Experiment.mean_bind,Experiment.mean_map,ih]
    congr 1; funext b
    congr 1; funext cs
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
noncomputable def traverse {f : A → Experiment B} (F : Realizer f) : Realizer (traverseM f) :=
  (composition (composition (deterministic (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List B))))
    (fold (collectStepRealizer F))) (deterministic TreeTyped.reverse)).congr (by
      intro as h
      simp only [Experiment.mean_bind,Experiment.mean]
      rw [mean_fold_collect]
      simp only [List.append_nil,List.reverse_reverse,id_eq])
omit [Codec A] [Codec B] in
lemma all_traverse (f : A → Experiment B) (as : List A) (P : B → Prop)
    (hf : ∀ a∈as,(f a).All P) : (traverseM f as).All (fun bs=>∀ b∈bs,P b) := by
  induction as with
  | nil => simp [traverseM,Experiment.All]
  | cons a as ih =>
    rw [traverseM,Experiment.all_bind]
    exact (hf a (by simp)).mono (fun b hb=>by
      rw [Experiment.all_map]
      exact (ih (fun a ha=>hf a (by simp [ha]))).mono (fun bs hbs=>by
        intro c hc
        rcases List.mem_cons.mp hc with rfl|hc
        · exact hb
        · exact hbs c hc))
omit [Codec A] [Codec B] in
lemma all_traverse_length (f : A → Experiment B) (as : List A) :
    (traverseM f as).All (fun bs=>bs.length=as.length) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [traverseM,Experiment.all_bind]
    exact (Experiment.all_true (f a)).mono (fun b _=>by
      rw [Experiment.all_map]
      exact ih.mono (fun bs hb=>by simpa only [List.length_cons] using congrArg Nat.succ hb))
end MatchingFPRAS.OnlineTree

end OAI
