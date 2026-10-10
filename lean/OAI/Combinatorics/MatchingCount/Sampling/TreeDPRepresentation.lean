import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCount

namespace OAI

namespace MatchingFPRAS.ExecutableDP

lemma privateFlag_perm {b c : Bag} (h : b.Perm c) (l : ℕ) :
    privateFlag (l,b)=privateFlag (l,c) := by simp only [privateFlag,h.length_eq,h.mem_iff]
lemma sharedFlag_perm {b c : Bag} (h : b.Perm c) (l : ℕ) :
    sharedFlag (l,b)=sharedFlag (l,c) := by simp only [sharedFlag,privateFlag_perm h,h.mem_iff]
lemma totalFlag_perm {b c : Bag} (h : b.Perm c) (l : ℕ) :
    totalFlag (l,b)=totalFlag (l,c) := by simp only [totalFlag,h.mem_iff]

lemma forall₂_filter {A B : Type} {R : A → B → Prop} {as : List A} {bs : List B}
    (h : List.Forall₂ R as bs) (p : A → Bool) (q : B → Bool)
    (he : ∀ a b,R a b → p a=q b) : List.Forall₂ R (as.filter p) (bs.filter q) := by
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab hs ih =>
    simp only [List.filter_cons,he a b hab]
    cases q b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact ih
    · exact .cons hab ih

lemma privateNumber_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    privateNumber a l=privateNumber b l :=
  (forall₂_filter h _ _ (fun _ _ hh=>privateFlag_perm hh l)).length_eq
lemma sharedNumber_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    sharedNumber a l=sharedNumber b l :=
  (forall₂_filter h _ _ (fun _ _ hh=>sharedFlag_perm hh l)).length_eq
lemma totalNumber_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    totalNumber a l=totalNumber b l :=
  (forall₂_filter h _ _ (fun _ _ hh=>totalFlag_perm hh l)).length_eq
lemma trim_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (l : ℕ) :
    List.Forall₂ List.Perm (trim a l) (trim b l) :=
  forall₂_filter h _ _ (fun _ _ hh=>congrArg Bool.not (totalFlag_perm hh l))
lemma update_rows {a b : Bags} (h : List.Forall₂ List.Perm a b)
    (ps : Parents) (l m B : ℕ) (t : Table) :
    update (((a,ps),(l,t)),(m,B))=update (((b,ps),(l,t)),(m,B)) := by
  simp only [update,context,privateNumber_rows h,sharedNumber_rows h,totalNumber_rows h]
lemma run_rows {a b : Bags} (h : List.Forall₂ List.Perm a b)
    (p : Params) (ls : List ℕ) (t : Table) :
    (runState p ls a t).2=(runState p ls b t).2 := by
  induction ls generalizing a b t with
  | nil => rfl
  | cons l ls ih =>
    simp only [runState,update_rows h]
    exact ih (trim_rows h l) _
lemma count_rows {a b : Bags} (h : List.Forall₂ List.Perm a b) (ps : Parents) (ls : List ℕ) :
    count ((a,ps),ls)=count ((b,ps),ls) := by
  simp only [count,run,h.length_eq,run_rows h]
lemma run_perm {a b : Bags} (h : a.Perm b) (p : Params) (ls : List ℕ) (t : Table) :
    (runState p ls a t).2=(runState p ls b t).2 := by
  induction ls generalizing a b t with
  | nil => rfl
  | cons l ls ih =>
    simp only [runState,update_perm h]
    exact ih (h.filter _) _
lemma count_perm {a b : Bags} (h : a.Perm b) (ps : Parents) (ls : List ℕ) :
    count ((a,ps),ls)=count ((b,ps),ls) := by
  simp only [count,run,h.length_eq,run_perm h]

noncomputable def orderedRep {n m : ℕ} (bags : Fin n → Finset (Fin m)) : Bags :=
  List.ofFn (fun i=>bagRep (bags i))

lemma orderedRep_perm {n m : ℕ} (bags : Fin n → Finset (Fin m)) :
    (orderedRep bags).Perm (activeRep bags Finset.univ) := by
  unfold orderedRep activeRep
  change (List.ofFn ((bagRep ∘ bags) ∘ id)).Perm _
  rw [← List.map_ofFn]
  apply List.Perm.map
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact List.nodup_ofFn.mpr Function.injective_id
  · exact Finset.nodup_toList _
  · ext i; simp

lemma count_ordered {n m : ℕ} (bags : Fin n → Finset (Fin m))
    (parent : Fin m → Option (Fin m)) (ls : List (Fin m)) :
    count ((orderedRep bags,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls := by
  rw [count_perm (orderedRep_perm bags),count_eq]

lemma count_represented {n m : ℕ} (bags : Fin n → Finset (Fin m))
    (parent : Fin m → Option (Fin m)) (ls : List (Fin m)) (bs : Bags)
    (hbs : List.Forall₂ List.Perm bs (orderedRep bags)) :
    count ((bs,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls := by
  rw [count_rows hbs,count_ordered]

end MatchingFPRAS.ExecutableDP

end OAI
