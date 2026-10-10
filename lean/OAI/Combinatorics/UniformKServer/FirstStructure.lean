import Mathlib

namespace OAI

                                     
section

/-! Precedence across heavy balls, chronological tiers, and singleton fallback.
A qualifying prefix covers the request, so fallback does not contribute to the
short-edge separation estimate. -/
noncomputable section
namespace UniformKServer.FirstStructure
open scoped Classical
variable {I J : Type*}

def first : List I → (I → Option J) → Option J
  | [], _ => none
  | i::is, f => (f i).or (first is f)

def key (is : List I) (f : I → Option J) (z : J) : J := (first is f).getD z

def indicator (x y : J) : ℝ := if x=y then 0 else 1

theorem indicator_bounds (x y : J) : indicator x y ∈ Set.Icc (0:ℝ) 1 := by
  unfold indicator
  split_ifs <;> constructor <;> norm_num

theorem first_append (is js : List I) (f : I → Option J) :
    first (is++js) f=(first is f).or (first js f) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append,first,ih]
    cases f i <;> rfl

theorem first_eq_some (is : List I) (f : I → Option J)
    (h : ∃ i∈is, (f i).isSome=true) : ∃ j, first is f=some j := by
  induction is with
  | nil => simp at h
  | cons i is ih =>
    cases he : f i with
    | some j => exact ⟨j,by simp only [first,he,Option.some_or]⟩
    | none =>
      have ht : ∃ j∈is, (f j).isSome=true := by
        obtain ⟨j,hj,hf⟩ := h
        rcases List.mem_cons.mp hj with rfl|hj
        · simp only [he,Option.isSome_none,Bool.false_eq_true] at hf
        · exact ⟨j,hj,hf⟩
      obtain ⟨j,hj⟩ := ih ht
      exact ⟨j,by simp only [first,he,Option.none_or,hj]⟩

theorem equal_covered_prefix (is js : List I) (f g : I → Option J) (x y : J)
    (h : ∀ i∈is, f i=g i) (hc : ∃ i∈is, (f i).isSome=true) :
    key (is++js) f x=key (is++js) g y := by
  have he : first is f=first is g := by
    clear hc
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [first,first,h i (by simp),ih (fun j hj => h j (by simp [hj]))]
  obtain ⟨j,hj⟩ := first_eq_some is f hc
  simp only [key,first_append,hj,←he,Option.some_or,Option.getD_some]

theorem covered_prefix_bound (is js : List I) (f g : I → Option J) (x y : J)
    (hc : ∃ i∈is, (f i).isSome=true) :
    indicator (key (is++js) f x) (key (is++js) g y)≤
      (is.map (fun i => indicator (f i) (g i))).sum := by
  by_cases he : ∀ i∈is, f i=g i
  · rw [equal_covered_prefix is js f g x y he hc]
    simp only [indicator]
    exact List.sum_nonneg (fun a ha => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      exact (indicator_bounds _ _).1)
  · push Not at he
    obtain ⟨i,hi,hne⟩ := he
    apply (indicator_bounds _ _).2.trans
    have hm : indicator (f i) (g i) ∈ is.map (fun j => indicator (f j) (g j)) := List.mem_map.mpr ⟨i,hi,rfl⟩
    have hs := List.single_le_sum (l:=is.map (fun j => indicator (f j) (g j)))
      (fun a ha => by
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
        exact (indicator_bounds _ _).1) (indicator (f i) (g i)) hm
    simpa only [indicator,ite_eq_right hne] using hs

theorem indicator_map (f : I → J) (a b : I) : indicator (f a) (f b)≤ indicator a b := by
  by_cases he : a=b
  · subst b; simp [indicator]
  · simpa only [indicator,ite_eq_right he] using (indicator_bounds (f a) (f b)).2

end UniformKServer.FirstStructure

end


end

end OAI
