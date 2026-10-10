import Mathlib

namespace OAI

noncomputable section

namespace KKLocalPatching.Colored

noncomputable section

variable {A : Type*}

abbrev Cell (A : Type*) := (A × ℤ) × Bool

def old (s : List (A × ℤ)) : List (Cell A) := s.map (fun z => (z,false))

def changes : List (A × ℤ) → List (List (Cell A))
  | [] => []
  | z::s => ((changes s).map (fun c => (z,false)::c)) ++
      ((old s::changes s).map (fun c => (z,true)::c))

def erase (c : List (Cell A)) : List (A × ℤ) := c.map Prod.fst

@[simp] theorem erase_old (s : List (A × ℤ)) : erase (old s)=s := by
  simp [erase,old,List.map_map,Function.comp_def]

theorem changes_length (s : List (A × ℤ)) : (changes s).length+1=2^s.length := by
  induction s with
  | nil => simp [changes]
  | cons z s ih =>
    simp only [changes,List.length_append,List.length_map,List.length_cons,pow_succ]
    omega

theorem erase_of_mem_changes {s : List (A × ℤ)} {c : List (Cell A)} (hc : c∈changes s) : erase c=s := by
  induction s generalizing c with
  | nil => simp [changes] at hc
  | cons z s ih =>
    simp only [changes,List.mem_append,List.mem_map] at hc
    rcases hc with ⟨d,hd,rfl⟩ | ⟨d,hd,rfl⟩
    · simpa only [erase,List.map_cons] using congrArg (List.cons z) (ih hd)
    · rcases List.mem_cons.mp hd with rfl | hd
      · change z::erase (old s)=z::s
        rw [erase_old]
      · simpa only [erase,List.map_cons] using congrArg (List.cons z) (ih hd)

theorem true_of_mem_changes {s : List (A × ℤ)} {c : List (Cell A)} (hc : c∈changes s) :
    ∃ z∈c, z.2=true := by
  induction s generalizing c with
  | nil => simp [changes] at hc
  | cons z s ih =>
    simp only [changes,List.mem_append,List.mem_map] at hc
    rcases hc with ⟨d,hd,rfl⟩ | ⟨d,hd,rfl⟩
    · obtain ⟨a,ha,h⟩ := ih hd
      exact ⟨a,List.mem_cons_of_mem _ ha,h⟩
    · exact ⟨(z,true),List.mem_cons_self,rfl⟩

def value [Ring A] (u v : ℤ → A) (c : List (Cell A)) : A :=
  (c.map (fun z => z.1.1*(if z.2 then v z.1.2 else u z.1.2))).prod

@[simp] theorem value_nil [Ring A] (u v : ℤ → A) : value u v []=1 := rfl

@[simp] theorem value_cons [Ring A] (u v : ℤ → A) (z : Cell A) (c : List (Cell A)) :
    value u v (z::c)=z.1.1*(if z.2 then v z.1.2 else u z.1.2)*value u v c := rfl

@[simp] theorem value_old [Ring A] (u v : ℤ → A) (s : List (A × ℤ)) :
    value u v (old s)=(s.map (fun z => z.1*u z.2)).prod := by
  simp [value,old,List.map_map,Function.comp_def]

theorem value_append [Ring A] (u v : ℤ → A) (s t : List (Cell A)) :
    value u v (s++t)=value u v s*value u v t := by
  simp only [value,List.map_append,List.prod_append]

theorem expansion [Ring A] (u v : ℤ → A) (s : List (A × ℤ)) :
    (s.map (fun z => z.1*(u z.2+v z.2))).prod=
      (s.map (fun z => z.1*u z.2)).prod+((changes s).map (value u v)).sum := by
  induction s with
  | nil => simp [changes]
  | cons z s ih =>
    simp only [changes,List.map_cons,List.prod_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,value_cons,Bool.false_eq_true,ite_false,ite_true,
      List.sum_cons,value_old,ih]
    simp only [List.sum_map_mul_left]
    noncomm_ring

end

end KKLocalPatching.Colored
end

end OAI
