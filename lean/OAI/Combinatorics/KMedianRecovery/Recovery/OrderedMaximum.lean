import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalRule

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
variable {E β : Type*} [LinearOrder β]
def run (score : E→β) (s : E) : List E→E
  | []=>s
  | a::as=>run score (if score s<score a then a else s) as
lemma mem (score : E→β) (s : E) (as : List E) : run score s as=s ∨ run score s as∈as := by
  induction as generalizing s with
  | nil=>exact Or.inl rfl
  | cons a as ih=>
    unfold run
    rcases ih (if score s<score a then a else s) with h|h
    · by_cases hs : score s<score a
      · simp only [ite_eq_left hs] at h
        simpa only [ite_eq_left hs] using Or.inr (List.mem_cons.mpr (Or.inl h))
      · simpa only [ite_eq_right hs] using Or.inl h
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))
lemma own_le (score : E→β) (s : E) (as : List E) : score s ≤ score (run score s as) := by
  induction as generalizing s with
  | nil=>exact le_rfl
  | cons a as ih=>
    unfold run
    by_cases hs : score s<score a
    · rw [ite_eq_left hs]
      exact hs.le.trans (ih a)
    · rw [ite_eq_right hs]
      exact ih s
lemma score_le (score : E→β) (s : E) (as : List E) (a : E) (ha : a∈as) : score a ≤ score (run score s as) := by
  induction as generalizing s with
  | nil=>exact False.elim (List.not_mem_nil ha)
  | cons b as ih=>
    unfold run
    rcases List.mem_cons.mp ha with rfl|ha
    · by_cases hs : score s<score a
      · rw [ite_eq_left hs]; exact own_le score a as
      · rw [ite_eq_right hs]; exact (le_of_not_gt hs).trans (own_le score s as)
    · exact ih (if score s<score b then b else s) ha
lemma fold (score : E→β) (s : E) (as : List E) :
    as.foldl (fun s a=>if score s<score a then a else s) s=run score s as := by
  induction as generalizing s with
  | nil=>rfl
  | cons a as ih=>exact ih _
def ofList (score : E→β) (as : List E) (h : as≠[]) : E := run score (as.head h) as.tail
lemma ofList_mem (score : E→β) (as : List E) (h : as≠[]) : ofList score as h∈as := by
  rcases mem score (as.head h) as.tail with he|he
  · rw [ofList,he]
    exact List.head_mem h
  · exact List.mem_of_mem_tail he
lemma le_ofList (score : E→β) (as : List E) (h : as≠[]) (a : E) (ha : a∈as) :
    score a ≤ score (ofList score as h) := by
  cases as with
  | nil=>exact False.elim (h rfl)
  | cons b as=>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact own_le score a as
    · exact score_le score b as a ha
lemma cast_run (score : E→ℚ) (s : E) (as : List E) :
    run (fun a=>(score a:ℝ)) s as=run score s as := by
  induction as generalizing s with
  | nil=>rfl
  | cons a as ih=>
    simp only [run,Rat.cast_lt,ih]
end MetricKMedianRecovery.OrderedMaximum

namespace MetricKMedianRecovery.Categorical.Selected
variable {E : Type*} [DecidableEq E] {a : ℕ}
def bag (es : List E) (part : E→Fin a) (j : Fin a) : List E := es.filter (fun e=>part e=j)
omit [DecidableEq E] in
lemma bag_ne_nil (es : List E) (he : ∀ e,e∈es) (part : E→Fin a)
    (hp : Function.Surjective part) (j : Fin a) : bag es part j≠[] := by
  obtain ⟨e,hem⟩:=hp j
  intro hn
  have hm : e∈bag es part j:=List.mem_filter.mpr ⟨he e,by simpa using hem⟩
  rw [hn] at hm
  exact List.not_mem_nil hm
noncomputable def orderedRule (es : List E) (he : ∀ e,e∈es) (part : E→Fin a)
    (hp : Function.Surjective part) : Rule part where
  choose score j:=OrderedMaximum.ofList score (bag es part j) (bag_ne_nil es he part hp j)
  spec score j:=by
    have hm := OrderedMaximum.ofList_mem score (bag es part j) (bag_ne_nil es he part hp j)
    refine ⟨by exact of_decide_eq_true (List.mem_filter.mp hm).2,?_⟩
    intro e hpart
    exact OrderedMaximum.le_ofList score (bag es part j) (bag_ne_nil es he part hp j) e
      (List.mem_filter.mpr ⟨he e,by simpa only [decide_eq_true_eq] using hpart⟩)
end MetricKMedianRecovery.Categorical.Selected

end OAI
