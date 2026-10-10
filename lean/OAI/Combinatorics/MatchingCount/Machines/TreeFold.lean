import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterControl
import OAI.Combinatorics.MatchingCount.Machines.TreeTyped

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]
namespace Fold
open RegisterControl (Instr Runs Effect)

inductive Point where | loop | check | splitHead | pushTail | pushArgs | body | popTail | rebuild | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.loop,.check,.splitHead,.pushTail,.pushArgs,.body,.popTail,.rebuild,.halt},by
  intro p; cases p <;> simp⟩
def code (P : Proc (K Reg)) : Point → RegisterControl.Instr Reg Point
  | .loop => .call (TreeFunction.split 1 0 (by decide)) .check
  | .check => .branch 1 .halt .splitHead
  | .splitHead => .call (TreeFunction.split 3 1 (by decide)) .pushTail
  | .pushTail => .call (TreeFunction.cons 1 2 (by decide)) .pushArgs
  | .pushArgs => .call (TreeFunction.cons 3 0 (by decide)) .body
  | .body => .call P .popTail
  | .popTail => .call (TreeFunction.split 1 2 (by decide)) .rebuild
  | .rebuild => .call (TreeFunction.cons 1 0 (by decide)) .loop
  | .halt => .halt

def heads (a b r s : Data) : Env Reg := Function.update (env b r s) 3 a
lemma splitHeads (a b r s : Data) :
    Exec (TreeFunction.split 3 1 (by decide)) (encodeEnv (env b (.cons a r) s)) (encodeEnv (heads a b r s))
      (2*TreeFunction.size a+5) := by
  have hh := split_exec (env b (.cons a r) s) 3 1 (by decide) () a r rfl
  have he : putPair (env b (.cons a r) s) 3 1 a r=heads a b r s := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  convert hh using 1
  all_goals try rfl
  simp [TreeFunction.size,env,TreeData.encode]
  omega
lemma pushTail (a b r s : Data) :
    Exec (TreeFunction.cons 1 2 (by decide)) (encodeEnv (heads a b r s)) (encodeEnv (heads a b .nil (.cons r s)))
      (2*TreeFunction.size r+3) := by
  have hh := cons_exec (heads a b r s) 1 2 (by decide) ()
  have he : putPair (heads a b r s) 1 2 .nil (.cons (heads a b r s 1) (heads a b r s 2))=
      heads a b .nil (.cons r s) := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  exact hh
lemma pushArgs (a b r s : Data) :
    Exec (TreeFunction.cons 3 0 (by decide)) (encodeEnv (heads a b .nil (.cons r s)))
      (encodeEnv (env (.cons a b) .nil (.cons r s))) (2*TreeFunction.size a+3) := by
  have hh := cons_exec (heads a b .nil (.cons r s)) 3 0 (by decide) ()
  have he : putPair (heads a b .nil (.cons r s)) 3 0 .nil
      (.cons (heads a b .nil (.cons r s) 3) (heads a b .nil (.cons r s) 0))=
      env (.cons a b) .nil (.cons r s) := by
    funext i; fin_cases i <;> simp [heads,putPair,env]
  rw [he] at hh
  exact hh

def cost (f : A×B → B) (t : A×B → ℕ) : List A → B → ℕ
  | [],_ => 10
  | a::as,b => t (a,b)+6*TreeFunction.size (encode a)+8*TreeFunction.size (encode as)+34+cost f t as (f (a,b))

lemma runs {f : A×B → B} (F : Realizer f) (as : List A) (b : B) (s : Data) :
    Runs (code F.program) (some Point.loop) (env (encode (as,b)) .nil s)
      (env (encode (as.foldl (fun b a=>f (a,b)) b)) .nil s) (cost f F.cost as b) := by
  induction as generalizing b with
  | nil =>
    have hh : Runs (code F.program) (some Point.halt) (env (encode b) .nil s) (env (encode b) .nil s) 1 :=
      Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hc : Runs (code F.program) (some Point.check) (env (encode b) .nil s) (env (encode b) .nil s) 2 :=
      Runs.step _ _ _ _ _ 1 1 (Effect.nilBranch _ 1 _ _ rfl) hh
    have hs:=split10 .nil (encode b) .nil s
    have hs' : Exec (TreeFunction.split 1 0 (by decide)) (encodeEnv (env (encode (([] : List A),b)) .nil s))
        (encodeEnv (env (encode b) .nil s)) 7 := by simpa [size_nil,encode_prod,encode_list_nil] using hs
    exact Runs.step _ _ _ _ _ 2 8 (Effect.call _ _ _ _ 7 hs') hc
  | cons a as ih =>
    let z:=as.foldl (fun b a=>f (a,b)) (f (a,b))
    let sa:=TreeFunction.size (encode a)
    let sr:=TreeFunction.size (encode as)
    let rest:=cost f F.cost as (f (a,b))
    have hr := ih (f (a,b))
    have h1:=cons10 (encode (f (a,b))) (encode as) s
    have hreb : Runs (code F.program) (some Point.rebuild) (env (encode (f (a,b))) (encode as) s)
        (env (encode z) .nil s) ((2*sr+4)+rest) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h1) hr
    have h2 := (split12 (encode (f (a,b))) .nil (encode as) s).mono
      (show TreeFunction.size Data.nil+2*TreeFunction.size (encode as)+4 ≤ 2*sr+5 by
        change 1+2*sr+4 ≤ 2*sr+5
        omega)
    have hpop : Runs (code F.program) (some Point.popTail) (env (encode (f (a,b))) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((2*sr+6)+((2*sr+4)+rest)) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h2) hreb
    have h3:=F.correct (a,b) (.cons (encode as) s)
    have hbody : Runs (code F.program) (some Point.body) (env (encode (a,b)) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h3) hpop
    have h4:=pushArgs (encode a) (encode b) (encode as) s
    have ha : Runs (code F.program) (some Point.pushArgs) (heads (encode a) (encode b) .nil (.cons (encode as) s))
        (env (encode z) .nil s) ((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h4) hbody
    have h5:=pushTail (encode a) (encode b) (encode as) s
    have ht : Runs (code F.program) (some Point.pushTail) (heads (encode a) (encode b) (encode as) s)
        (env (encode z) .nil s) ((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h5) ha
    have h6:=splitHeads (encode a) (encode b) (encode as) s
    have hsh : Runs (code F.program) (some Point.splitHead) (env (encode b) (encode (a::as)) s)
        (env (encode z) .nil s) ((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h6) ht
    have hc : Runs (code F.program) (some Point.check) (env (encode b) (encode (a::as)) s)
        (env (encode z) .nil s) (1+((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest))))))) :=
      Runs.step _ _ _ _ _ _ 1 (Effect.consBranch _ 1 _ _ (encode a) (encode as) rfl) hsh
    have h7 := (split10 (encode (a::as)) (encode b) .nil s).mono
      (show TreeFunction.size Data.nil+2*TreeFunction.size (encode (a::as))+4 ≤ 2*TreeFunction.size (encode (a::as))+5 by
        change 1+2*TreeFunction.size (encode (a::as))+4 ≤ 2*TreeFunction.size (encode (a::as))+5
        omega)
    have hl : Runs (code F.program) (some Point.loop) (env (encode (a::as,b)) .nil s)
        (env (encode z) .nil s) ((2*TreeFunction.size (encode (a::as))+6)+(1+((2*sa+6)+((2*sr+4)+((2*sa+4)+((F.cost (a,b)+1)+((2*sr+6)+((2*sr+4)+rest)))))))) :=
      Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ _ h7) hc
    convert hl using 1
    all_goals try rfl
    simp only [cost,encode_list_cons,size_cons,sa,sr,rest]
    ring
end Fold

def fold {f : A×B → B} (F : Realizer f) : Realizer (fun ab : List A×B=>ab.1.foldl (fun b a=>f (a,b)) ab.2) where
  program := RegisterControl.compile (Fold.code F.program)
  cost := fun ab=>Fold.cost f F.cost ab.1 ab.2
  correct := fun ab s=>RegisterControl.compile_exec _ _ _ _ (Fold.runs F ab.1 ab.2 s)
end MatchingFPRAS.TreeTyped

end OAI
