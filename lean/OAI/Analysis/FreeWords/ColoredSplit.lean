import Mathlib
import OAI.Analysis.FreeWords.ColoredExpansion

namespace OAI

noncomputable section

namespace KKLocalPatching.Colored

noncomputable section

variable {A : Type*}

theorem first_true_split (c : List (Cell A)) (hc : ∃ z∈c, z.2=true) :
    ∃ p z r, c=old p++(z,true)::r := by
  induction c with
  | nil => simp at hc
  | cons a c ih =>
    rcases a with ⟨z,b⟩
    cases b
    · have ht : ∃ z∈c, z.2=true := by
        obtain ⟨a,ha,ha'⟩ := hc
        rcases List.mem_cons.mp ha with rfl | ha
        · simp at ha'
        · exact ⟨a,ha,ha'⟩
      obtain ⟨p,y,r,hr⟩ := ih ht
      refine ⟨z::p,y,r,?_⟩
      simp only [old,List.map_cons,List.cons_append,hr]
    · exact ⟨[],z,c,rfl⟩

theorem eq_old_of_no_true (c : List (Cell A)) (hc : ¬∃ z∈c, z.2=true) : c=old (erase c) := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    rcases a with ⟨z,b⟩
    have ht : ¬∃ a∈c, a.2=true := by
      rintro ⟨a,ha,h⟩
      exact hc ⟨a,List.mem_cons_of_mem _ ha,h⟩
    cases b
    · simpa only [erase,List.map_cons,old] using congrArg (List.cons (z,false)) (ih ht)
    · exact (hc ⟨(z,true),List.mem_cons_self,rfl⟩).elim

inductive Split (c : List (Cell A)) where
  | single (p : List (A × ℤ)) (z : A × ℤ) (s : List (A × ℤ))
      (eqn : c=old p++(z,true)::old s)
  | multiple (p : List (A × ℤ)) (z : A × ℤ) (g : List (A × ℤ))
      (y : A × ℤ) (r : List (Cell A))
      (eqn : c=old p++(z,true)::(old g++(y,true)::r))

theorem split_nonempty {c : List (Cell A)} (hc : ∃ z∈c, z.2=true) : Nonempty (Split c) := by
  classical
  obtain ⟨p,z,r,he⟩ := first_true_split c hc
  by_cases hr : ∃ a∈r, a.2=true
  · obtain ⟨g,y,s,hs⟩ := first_true_split r hr
    exact ⟨.multiple p z g y s (he.trans (by rw [hs]))⟩
  · exact ⟨.single p z (erase r) (he.trans (by rw [← eq_old_of_no_true r hr]))⟩

def split {s : List (A × ℤ)} {c : List (Cell A)} (hc : c∈changes s) : Split c :=
  Classical.choice (split_nonempty (true_of_mem_changes hc))

namespace Split

variable [Ring A] {c : List (Cell A)}

def exponent : Split c → ℤ
  | .single _ z _ _ => z.2
  | .multiple _ _ _ _ _ _ => 1

def gap (u : ℤ → A) : Split c → A
  | .single _ _ _ _ => 0
  | .multiple _ _ g y _ _ => (g.map (fun z => z.1*u z.2)).prod*y.1

def coefficient (u : ℤ → A) (right : A) : Split c → A
  | .single p z s _ => (s.map (fun z => z.1*u z.2)).prod*right*
      (p.map (fun z => z.1*u z.2)).prod*z.1
  | .multiple _ _ _ _ _ _ => 0

end Split

end

end KKLocalPatching.Colored
end

end OAI
