import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeCompiler

namespace OAI

namespace MatchingFPRAS.TreeData
open Data

def ofList : List Data → Data
  | [] => .nil
  | x::xs => .cons x (ofList xs)
def unary : ℕ → Data
  | 0 => .nil
  | n+1 => .cons .nil (unary n)
lemma ofList_nil : ofList []=.nil := rfl
lemma ofList_cons (x : Data) (xs : List Data) : ofList (x::xs)=.cons x (ofList xs) := rfl
lemma unary_encode_length (n : ℕ) : (encode (unary n)).length=2*n+1 := by
  induction n <;> simp_all [unary,encode]; omega
lemma encode_head_le (x y : Data) : (encode x).length≤(encode (.cons x y)).length := by
  simp only [encode,List.length_cons,List.length_append]; omega
lemma encode_tail_le (x y : Data) : (encode y).length≤(encode (.cons x y)).length := by
  simp only [encode,List.length_cons,List.length_append]; omega
end MatchingFPRAS.TreeData
namespace MatchingFPRAS.TreeMachine
open TreeData RegisterProc Turing MachineCost

variable {R : Type} [DecidableEq R]
lemma SizeBound.update {E : Env R} {B : ℕ} (h : SizeBound E B) (i : R) (x : Data)
    (hx : (encode x).length≤B) : SizeBound (Function.update E i x) B := by
  intro j
  by_cases hh : j=i
  · subst j; simpa using hx
  · simpa only [Function.update_of_ne hh] using h j
lemma SizeBound.putPair {E : Env R} {B : ℕ} (h : SizeBound E B) (i j : R) (x y : Data)
    (hx : (encode x).length≤B) (hy : (encode y).length≤B) : SizeBound (putPair E i j x y) B :=
  (h.update i x hx).update j y hy
lemma SizeBound.split {E : Env R} {B : ℕ} (h : SizeBound E B) (i j : R) (x y : Data)
    (he : E j=.cons x y) : SizeBound (TreeMachine.putPair E i j x y) B := by
  have hh:=h j
  rw [he] at hh
  exact h.putPair i j x y ((encode_head_le x y).trans hh) ((encode_tail_le x y).trans hh)
end MatchingFPRAS.TreeMachine

namespace MatchingFPRAS.TreeLookup
open TreeData TreeMachine RegisterProc

inductive Point where
  | loop | check | dec | tail | finish | found | missing | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.loop,.check,.dec,.tail,.finish,.found,.missing,.halt},by intro p; cases p <;> simp⟩
abbrev R := Fin 4

def program : Point → Instr R Point
  | .loop => .branch 0 .finish .check
  | .check => .branch 1 .missing .dec
  | .dec => .split 2 0 (by decide) .tail
  | .tail => .split 2 1 (by decide) .loop
  | .finish => .branch 1 .missing .found
  | .found => .split 2 1 (by decide) .halt
  | .missing => .nil 2 .halt
  | .halt => .halt

def result (E : Env R) : ℕ → List Data → Env R
  | 0,[] => Function.update E 2 .nil
  | 0,x::xs => putPair E 2 1 x (ofList xs)
  | _+1,[] => Function.update E 2 .nil
  | n+1,x::xs => result (putPair (putPair E 2 0 .nil (unary n)) 2 1 x (ofList xs)) n xs

def steps : ℕ → List Data → ℕ
  | 0,_ => 4
  | _+1,[] => 4
  | n+1,_::xs => steps n xs+4
lemma steps_le (n : ℕ) (xs : List Data) : steps n xs≤4*(n+1) := by
  induction n generalizing xs with
  | zero => simp [steps]
  | succ n ih =>
    cases xs with
    | nil => simp only [steps]; omega
    | cons x xs => have hh:=ih xs; simp only [steps]; omega

lemma output (E : Env R) (n : ℕ) (xs : List Data) : result E n xs 2=xs.getD n .nil := by
  induction n generalizing E xs with
  | zero => cases xs <;> simp [result,putPair,List.getD]
  | succ n ih => cases xs with
    | nil => simp [result,List.getD]
    | cons x xs => simpa only [result,List.getD_cons_succ] using ih _ _

lemma nil_bound {E : Env R} {B : ℕ} (h : SizeBound E B) : (encode Data.nil).length≤B := by
  have hp:=encode_length_pos (E 0)
  have hh:=h 0
  simp only [encode,List.length_singleton]
  omega
lemma halt_runs (E : Env R) (B : ℕ) (h : SizeBound E B) : Runs program B (some Point.halt) E E 1 := by
  exact Runs.step (M:=program) Point.halt E none E E 0 h (Effect.halt E) (.done E)
lemma missing_runs (E : Env R) (B : ℕ) (h : SizeBound E B) :
    Runs program B (some Point.missing) E (Function.update E 2 .nil) 2 := by
  exact Runs.step (M:=program) Point.missing E (some Point.halt) _ _ 1 h (.nil E 2 Point.halt)
    (halt_runs _ B (h.update 2 .nil (nil_bound h)))
lemma found_runs (E : Env R) (B : ℕ) (h : SizeBound E B) (x y : Data) (he : E 1=.cons x y) :
    Runs program B (some Point.found) E (putPair E 2 1 x y) 2 := by
  exact Runs.step (M:=program) Point.found E (some Point.halt) _ _ 1 h (.split E 2 1 (by decide) Point.halt x y he)
    (halt_runs _ B (h.split 2 1 x y he))

theorem runs (n : ℕ) (xs : List Data) (E : Env R) (B : ℕ) (h : SizeBound E B)
    (hn : E 0=unary n) (hs : E 1=ofList xs) :
    Runs program B (some Point.loop) E (result E n xs) (steps n xs) ∧
      SizeBound (result E n xs) B := by
  induction n generalizing E xs with
  | zero =>
    have hn' : E 0=Data.nil := hn
    cases xs with
    | nil =>
      constructor
      · exact Runs.step (M:=program) Point.loop E (some Point.finish) E _ 3 h (.nilBranch E 0 Point.finish Point.check hn')
          (Runs.step (M:=program) Point.finish E (some Point.missing) E _ 2 h (.nilBranch E 1 Point.missing Point.found hs)
            (missing_runs E B h))
      · exact h.update 2 .nil (nil_bound h)
    | cons x xs =>
      have hs' : E 1=.cons x (ofList xs) := hs
      constructor
      · exact Runs.step (M:=program) Point.loop E (some Point.finish) E _ 3 h (.nilBranch E 0 Point.finish Point.check hn')
          (Runs.step (M:=program) Point.finish E (some Point.found) E _ 2 h (.consBranch E 1 Point.missing Point.found x (ofList xs) hs')
            (found_runs E B h x (ofList xs) hs'))
      · exact h.split 2 1 x (ofList xs) hs'
  | succ n ih =>
    have hn' : E 0=.cons .nil (unary n) := hn
    cases xs with
    | nil =>
      constructor
      · exact Runs.step (M:=program) Point.loop E (some Point.check) E _ 3 h (.consBranch E 0 Point.finish Point.check .nil (unary n) hn')
          (Runs.step (M:=program) Point.check E (some Point.missing) E _ 2 h (.nilBranch E 1 Point.missing Point.dec hs)
            (missing_runs E B h))
      · exact h.update 2 .nil (nil_bound h)
    | cons x xs =>
      have hs' : E 1=.cons x (ofList xs) := hs
      let F:=putPair E 2 0 .nil (unary n)
      let G:=putPair F 2 1 x (ofList xs)
      have hF : SizeBound F B := h.split 2 0 .nil (unary n) hn'
      have hF1 : F 1=.cons x (ofList xs) := by simpa [F,putPair] using hs'
      have hG : SizeBound G B := hF.split 2 1 x (ofList xs) hF1
      have hG0 : G 0=unary n := by simp [G,F,putPair]
      have hG1 : G 1=ofList xs := by simp [G,putPair]
      obtain ⟨hr,hout⟩:=ih xs G hG hG0 hG1
      constructor
      · have hh:=Runs.step (M:=program) Point.tail F (some Point.loop) G _ (steps n xs) hF
          (.split F 2 1 (by decide) Point.loop x (ofList xs) hF1) hr
        have hh':=Runs.step (M:=program) Point.dec E (some Point.tail) F _ (steps n xs+1) h
          (.split E 2 0 (by decide) Point.tail .nil (unary n) hn') hh
        have hh'':=Runs.step (M:=program) Point.check E (some Point.dec) E _ (steps n xs+2) h
          (.consBranch E 1 Point.missing Point.dec x (ofList xs) hs') hh'
        exact Runs.step Point.loop E (some Point.check) E _ (steps n xs+3) h
          (.consBranch E 0 Point.finish Point.check .nil (unary n) hn') hh''
      · exact hout

theorem stack_exec (n : ℕ) (xs : List Data) (E : Env R) (B : ℕ) (h : SizeBound E B)
    (hn : E 0=unary n) (hs : E 1=ofList xs) :
    Exec (compile program) (encodeEnv E) (encodeEnv (result E n xs)) (20*(n+1)*(B+1)) := by
  have hh:=compile_exec program B (steps n xs) E _ (runs n xs E B h hn hs).1
  apply hh.mono
  have hk:=Nat.mul_le_mul_right (5*(B+1)) (steps_le n xs)
  nlinarith
end MatchingFPRAS.TreeLookup

end OAI
