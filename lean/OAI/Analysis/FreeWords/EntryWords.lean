import Mathlib

namespace OAI

noncomputable section

namespace KKRelativeMatrix

noncomputable section

variable {A : Type*} {n : ℕ}

def entryWords (s : List (ℤ × Matrix (Fin n) (Fin n) A)) (i j : Fin n) : List (List (ℤ × A)) :=
  match s with
  | [] => if i=j then [[]] else []
  | z::t => (List.finRange n).flatMap fun k => (entryWords t k j).map fun v => (z.1,z.2 i k)::v

theorem entryWords_length {s : List (ℤ × Matrix (Fin n) (Fin n) A)} {i j : Fin n}
    {v : List (ℤ × A)} (hv : v∈entryWords s i j) : v.length=s.length := by
  induction s generalizing i j v with
  | nil =>
    simp only [entryWords] at hv
    split_ifs at hv with h
    · simp only [List.mem_singleton] at hv
      subst v
      rfl
    · simp at hv
  | cons z s ih =>
    obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp hv
    obtain ⟨v,hv0,rfl⟩ := List.mem_map.mp hk
    simp only [List.length_cons,ih hv0]

theorem entryWords_letters {s : List (ℤ × Matrix (Fin n) (Fin n) A)} {i j : Fin n}
    {v : List (ℤ × A)} (hv : v∈entryWords s i j) :
    ∀ y∈v, ∃ z∈s, ∃ a b : Fin n, y=(z.1,z.2 a b) := by
  induction s generalizing i j v with
  | nil =>
    have h := entryWords_length hv
    have he : v=[] := List.eq_nil_of_length_eq_zero h
    simp [he]
  | cons z s ih =>
    obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp hv
    obtain ⟨v,hv0,rfl⟩ := List.mem_map.mp hk
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨z,List.mem_cons_self,i,k,rfl⟩
    · obtain ⟨z,hz,a,b,hy⟩ := ih hv0 y hy
      exact ⟨z,List.mem_cons_of_mem _ hz,a,b,hy⟩

theorem sum_map_flatMap {α β C : Type*} [AddMonoid C]
    (l : List α) (f : α → List β) (g : β → C) :
    ((l.flatMap f).map g).sum=(l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

def scalarWord [Monoid A] (u : ℤ → A) (s : List (ℤ × A)) : A :=
  (s.map (fun z => u z.1*z.2)).prod

@[simp] theorem scalarWord_cons [Monoid A] (u : ℤ → A) (z : ℤ × A) (s) :
    scalarWord u (z::s)=u z.1*z.2*scalarWord u s := rfl

def matrixWord [Semiring A] (u : ℤ → A) (s : List (ℤ × Matrix (Fin n) (Fin n) A)) :
    Matrix (Fin n) (Fin n) A :=
  (s.map (fun z => Matrix.diagonal (fun _ : Fin n => u z.1)*z.2)).prod

theorem entryWords_sum [Semiring A] (u : ℤ → A)
    (s : List (ℤ × Matrix (Fin n) (Fin n) A)) (i j : Fin n) :
    matrixWord u s i j=((entryWords s i j).map (scalarWord u)).sum := by
  induction s generalizing i j with
  | nil =>
    simp only [matrixWord,List.map_nil,List.prod_nil,Matrix.one_apply,entryWords]
    split_ifs <;> simp [scalarWord]
  | cons z s ih =>
    change ((Matrix.diagonal (fun _ : Fin n => u z.1)*z.2)*matrixWord u s) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_mul,ih,entryWords,sum_map_flatMap,List.map_map,
      Function.comp_def,scalarWord_cons,List.sum_map_mul_left]
    rw [← List.ofFn_eq_map,List.sum_ofFn]

theorem norm_list_sum_le {C : Type*} [SeminormedAddCommGroup C] (l : List C) :
    ‖l.sum‖≤(l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa only [List.sum_cons,List.map_cons] using (norm_add_le a l.sum).trans (add_le_add le_rfl ih)

end

end KKRelativeMatrix
end

end OAI
