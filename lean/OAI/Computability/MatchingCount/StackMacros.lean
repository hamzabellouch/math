import OAI.Computability.MatchingCount.FiniteStack

namespace OAI

section

namespace BinaryMatching.StackCode
namespace Block
variable {r : ℕ}

private theorem option_map_elim {α β : Type} (f : α → β) :
    Option.map f = fun q => q.elim none (some ∘ f) := by funext q; cases q <;> rfl

theorem cases_runs_empty (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : s k=[]) (he : e.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := he.map (cases k e z o).code (Sum.inr ∘ Sum.inl) none (by
    intro l
    change (e.code l).map _ = (e.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,List.head?_nil,Option.elim_none,Option.elim_some,
    Function.comp_apply] using h

theorem cases_runs_false (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some false) (hz : z.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := hz.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (by
    intro l
    change (z.code l).map _ = (z.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,Bool.false_eq_true,ite_false] using h

theorem cases_runs_true (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some true) (ho : o.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := ho.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (by
    intro l
    change (o.code l).map _ = (o.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,ite_true] using h

theorem loop_runs_empty (k : Fin r) (b : Block r) (s : Store r) (hs : s k=[]) :
    (loop k b).Runs s s 1 := by
  apply Steps.next
  simp only [loop,Instr.eval,hs,List.head?_nil,Option.elim_none]
  exact .refl _ _

theorem loop_runs_step (k : Fin r) (b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (hs : s k≠[]) (hb : b.Runs s s' t) (hl : (loop k b).Runs s' s'' u) :
    (loop k b).Runs s s'' (t+u+1) := by
  apply Steps.next
  have h := hb.map (loop k b).code Sum.inr (some (Sum.inl ())) (fun _ => rfl)
  have hh := h.trans hl
  cases he : s k with
  | nil => exact (hs he).elim
  | cons a l =>
    cases a <;> simpa only [loop,Instr.eval,he,List.head?_cons,Option.elim_none,
      Option.elim_some,Function.comp_apply,Bool.false_eq_true,ite_false,ite_true] using hh

def skip : Block r := primitive (.go ())
def push (k : Fin r) (b : Bool) : Block r := primitive (.push k b ())
def pop (k : Fin r) : Block r := primitive (.pop k ())

theorem skip_runs (s : Store r) : skip.Runs s s 1 := primitive_runs _ s

theorem push_runs (k : Fin r) (b : Bool) (s : Store r) :
    (push k b).Runs s (Function.update s k (b::s k)) 1 := primitive_runs _ s

theorem pop_runs (k : Fin r) (s : Store r) :
    (pop k).Runs s (Function.update s k (s k).tail) 1 := primitive_runs _ s

def clear (k : Fin r) : Block r := loop k (pop k)

theorem clear_runs (k : Fin r) (s : Store r) :
    (clear k).Runs s (Function.update s k []) (2*(s k).length+1) := by
  generalize hl : s k=l
  induction l generalizing s with
  | nil =>
    have he : Function.update s k []=s := by rw [←hl,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty k (pop k) s hl
  | cons a l ih =>
    let s' := Function.update s k l
    have hi := ih s' (by simp [s'])
    have hp : (pop k).Runs s s' 1 := by simpa [s',hl] using pop_runs k s
    have hx := loop_runs_step k (pop k) (by simp [hl]) hp hi
    have ht : 1+(2*l.length+1)+1=2*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    simpa only [clear,s',Function.update_idem] using hx

def moveBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq (push dst false)) ((pop src).seq (push dst true))

def reverseInto (src dst : Fin r) : Block r := loop src (moveBody src dst)

theorem moveBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (a : Bool) (l : List Bool)
    (hs : s src=a::l) :
    (moveBody src dst).Runs s (Function.update (Function.update s src l) dst (a::s dst)) 3 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have ht := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at ht
  have hseq : ((pop src).seq (push dst a)).Runs s
      (Function.update (Function.update s src l) dst (a::s dst)) 2 := by
    exact seq_runs _ _ hp ht
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

theorem reverseInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (reverseInto src dst).Runs s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
      (4*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst ([].reverse++s dst)=s := by
      rw [←hl,Function.update_eq_self]
      simp [hl]
    rw [he]
    exact loop_runs_empty src (moveBody src dst) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update s src l) dst (a::s dst)
    have hs' : s' src=l := by simp [s',hne]
    have hi := ih s' hs'
    have hm := moveBody_runs src dst hne s a l hl
    have hx := loop_runs_step src (moveBody src dst) (by simp [hl]) hm hi
    have he : Function.update (Function.update s' src []) dst (l.reverse++s' dst)=
        Function.update (Function.update s src []) dst ((a::l).reverse++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hks : k=src
        · subst k; simp [hne,s']
        · simp [Function.update_of_ne,hk,hks,s']
    rw [he] at hx
    have ht : 3+(4*l.length+1)+1=4*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

end Block
end BinaryMatching.StackCode
end

end OAI
