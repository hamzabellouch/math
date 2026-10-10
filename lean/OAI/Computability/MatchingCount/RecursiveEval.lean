import OAI.Computability.MatchingCount.RawContractionCompiler

namespace OAI

section

namespace BinaryMatching.RecursiveEval

inductive Branch (A B C : Type) where
  | leaf : B → Branch A B C
  | fork : C → A → A → Branch A B C

inductive Command (A C : Type) where
  | call : ℕ → A → Command A C
  | join : C → Command A C

abbrev State (A B C : Type) := List (Command A C) × List B

variable {A B C : Type} (zero : B) (expand : A → Branch A B C)
  (combine : C → B → B → B)

def value : ℕ → A → B
  | 0,_ => zero
  | k+1,a => match expand a with
    | .leaf b => b
    | .fork c x y => combine c (value k x) (value k y)

def cost : ℕ → A → ℕ
  | 0,_ => 1
  | k+1,a => match expand a with
    | .leaf _ => 1
    | .fork _ x y => 2+cost k x+cost k y

def calls : ℕ → A → ℕ
  | 0,_ => 1
  | k+1,a => match expand a with
    | .leaf _ => 1
    | .fork _ x y => 1+calls k x+calls k y

def step (s : State A B C) : State A B C :=
  match s.1 with
  | [] => s
  | .call 0 _ :: w => (w,zero::s.2)
  | .call (k+1) a :: w => match expand a with
    | .leaf b => (w,b::s.2)
    | .fork c x y => (.call k x::.call k y::.join c::w,s.2)
  | .join c :: w => match s.2 with
    | y::x::v => (w,combine c x y::v)
    | _ => ([],s.2)

lemma cost_le_calls (k : ℕ) (a : A) : cost expand k a≤2*calls expand k a := by
  induction k generalizing a with
  | zero => simp [cost,calls]
  | succ k ih =>
    simp only [cost,calls]
    cases h : expand a with
    | leaf b => simp
    | fork c x y => dsimp only; have h₁ := ih x; have h₂ := ih y; omega

lemma runs (k : ℕ) (a : A) (w : List (Command A C)) (v : List B) :
    (step zero expand combine)^[cost expand k a] (.call k a::w,v)=
      (w,value zero expand combine k a::v) := by
  induction k generalizing a w v with
  | zero => simp [cost,step,value]
  | succ k ih =>
    cases h : expand a with
    | leaf b => simp [cost,step,value,h]
    | fork c x y =>
      rw [cost,h]
      dsimp only
      have he : 2+cost expand k x+cost expand k y=(1+cost expand k y)+cost expand k x+1 := by omega
      rw [he,Function.iterate_succ_apply]
      simp only [step,h]
      rw [Function.iterate_add_apply,ih,Function.iterate_add_apply,ih]
      simp only [Function.iterate_one,step,value,h]

lemma runs_extra (k : ℕ) (a : A) (N : ℕ) (hN : cost expand k a≤N) :
    (step zero expand combine)^[N] ([.call k a],[])=
      ([],[value zero expand combine k a]) := by
  have hn : N=(N-cost expand k a)+cost expand k a := by omega
  rw [hn,Function.iterate_add_apply,runs]
  apply Function.iterate_fixed
  rfl

end BinaryMatching.RecursiveEval
end

end OAI
