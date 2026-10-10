import Mathlib
import OAI.Combinatorics.UniformKServer.StackRun

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

def alternate : List Bool→List Bool
  | []=>[]
  | [a]=>[a]
  | a::_::xs=>a::alternate xs

 theorem alternate_length (xs : List Bool) : (alternate xs).length=(xs.length+1)/2 := by
  fun_induction alternate xs <;> simp_all only [List.length_nil,List.length_cons]
  omega

 theorem matches_alternate {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (bs : List Bool) (he : Even bs.length) :
    Matches P (run P s (alternate bs)) ((machine P).run z bs) := by
  induction bs using alternate.induct generalizing s z with
  | case1=>exact h
  | case2 a=>simp at he
  | case3 a b bs ih=>
    have hb : Even bs.length:=by
      obtain ⟨c,hc⟩:=he
      refine ⟨c-1,?_⟩
      simp only [List.length_cons] at hc
      omega
    exact ih _ _ (matches_step P s z h a b) hb

 theorem alternate_get (bs : List Bool) (i : ℕ) (hi : 2*i<bs.length) :
    (alternate bs)[i]'(by rw [alternate_length];omega)=bs[2*i] := by
  induction bs using alternate.induct generalizing i with
  | case1=>simp at hi
  | case2 a=>have hh : i=0:=by simp only [List.length_cons,List.length_nil] at hi;omega
             subst i;rfl
  | case3 a b bs ih=>
    cases i with
    | zero=>rfl
    | succ i=>
      simpa only [alternate,List.getElem_cons_succ,show 2*(i+1)=2*i+2 by omega] using
        ih i (by simp only [List.length_cons] at hi;omega)

end UniformKServer.StackCompiler

end

end OAI
