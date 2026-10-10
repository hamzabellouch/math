import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeCompare
import OAI.Combinatorics.MatchingCount.Machines.RegisterStructured
import OAI.Combinatorics.MatchingCount.Machines.TreeTyped

namespace OAI

namespace MatchingFPRAS.TreeFunction
open TreeData TreeMachine RegisterProc

lemma split02 (x y a s : Data) :
    Exec (split 0 2 (by decide)) (encodeEnv (env x y (.cons a s)))
      (encodeEnv (env a y s)) (size x+2*size a+4) := by
  simpa only [putPair,env_update0,env_update2,env0,env2,size,split] using
    split_exec (env x y (.cons a s)) 0 2 (by decide) () a s rfl
end MatchingFPRAS.TreeFunction

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def choose {f : A → Bool} {g h : A → B} (F : Realizer f) (G : Realizer g) (H : Realizer h) :
    Realizer (fun a=>if f a then g a else h a) where
  program := seq (TreeFunction.copy 0 1 (by decide)) (seq (TreeFunction.cons 1 2 (by decide))
    (seq F.program (RegisterStructured.select 0
      (seq (TreeFunction.split 0 2 (by decide)) H.program)
      (seq (TreeFunction.split 0 2 (by decide)) G.program))))
  cost := fun a=>F.cost a+(if f a then G.cost a else H.cost a)+7*TreeFunction.size (encode a)+18
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split02 (encode (f a)) .nil (encode a) s
    have hs : TreeFunction.size (encode (f a)) ≤ 3 := by
      cases f a <;> simp [Codec.encode,bit]
    cases hf : f a
    · have h5:=H.correct a s
      have hh:=RegisterStructured.select_nil 0 _ (seq (TreeFunction.split 0 2 (by decide)) G.program) (env (encode (f a)) .nil (.cons (encode a) s))
        (env (encode (h a)) .nil s) _ (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh))).mono
      simp only [hf]
      simp only [size_nil]
      rw [hf] at hs
      omega
    · have h5:=G.correct a s
      have hh:=RegisterStructured.select_cons 0 (seq (TreeFunction.split 0 2 (by decide)) H.program) _ (env (encode (f a)) .nil (.cons (encode a) s))
        (env (encode (g a)) .nil s) _ .nil .nil (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh))).mono
      simp only [hf]
      simp only [size_nil]
      rw [hf] at hs
      omega

def less : Realizer (fun ab : ℕ×ℕ=>decide (ab.1<ab.2)) where
  program := seq (TreeFunction.split 1 0 (by decide))
    (seq (TreeArithmetic.less 1 0 (by decide))
      (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1)))
  cost := fun ab=>2*TreeFunction.size (nat ab.1)+3*(ab.1.bits.length+ab.2.bits.length)+31
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (nat a) (nat b) .nil s
    have h2:=TreeArithmetic.less_exec (env (nat b) (nat a) s) 1 0 (by decide) a b rfl rfl
    simp only [putPair,env_update0,env_update1] at h2
    have h3:=copy10 .nil (bit (decide (a<b))) s
    have h4:=clear1 (bit (decide (a<b))) (bit (decide (a<b))) s
    apply (h1.seq (h2.seq (h3.seq h4))).mono
    have hs : TreeFunction.size (bit (decide (a<b))) ≤ 3 := by
      cases decide (a<b) <;> simp [bit]
    simp only [size_nil]; omega

def constantData (x : Data) : Realizer (fun _ : A => x) :=
  match x with
  | .nil => ⟨TreeFunction.clear 0,fun a=>TreeFunction.size (encode a)+2,fun a s=>clear0 (encode a) .nil s⟩
  | .cons x y =>
    let P : Realizer (fun _ : A => (x,y)) := pair (constantData x) (constantData y)
    ⟨P.program,P.cost,P.correct⟩

def constant (b : B) : Realizer (fun _ : A=>b) :=
  let P : Realizer (fun _ : A=>encode b) := constantData (encode b)
  ⟨P.program,P.cost,P.correct⟩
end MatchingFPRAS.TreeTyped

end OAI
