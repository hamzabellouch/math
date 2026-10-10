import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeSubtract
import OAI.Combinatorics.MatchingCount.Machines.TreeChoice

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

def choosePartial (f : A → Bool) (g h : A → B) (F : Realizer f)
    (G H : Proc (K Reg)) (t u : A → ℕ)
    (hg : ∀ a s,f a=true → Exec G (encodeEnv (env (encode a) .nil s))
      (encodeEnv (env (encode (g a)) .nil s)) (t a))
    (hh : ∀ a s,f a=false → Exec H (encodeEnv (env (encode a) .nil s))
      (encodeEnv (env (encode (h a)) .nil s)) (u a)) :
    Realizer (fun a=>if f a then g a else h a) where
  program := seq (TreeFunction.copy 0 1 (by decide)) (seq (TreeFunction.cons 1 2 (by decide))
    (seq F.program (RegisterStructured.select 0
      (seq (TreeFunction.split 0 2 (by decide)) H)
      (seq (TreeFunction.split 0 2 (by decide)) G))))
  cost := fun a=>F.cost a+(if f a then t a else u a)+7*TreeFunction.size (encode a)+18
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split02 (encode (f a)) .nil (encode a) s
    have hs : TreeFunction.size (encode (f a)) ≤ 3 := by
      cases f a <;> simp [Codec.encode,bit]
    cases hf : f a
    · have h5:=hh a s hf
      have hh':=RegisterStructured.select_nil 0 _ (seq (TreeFunction.split 0 2 (by decide)) G)
        (env (encode (f a)) .nil (.cons (encode a) s)) (env (encode (h a)) .nil s) _
        (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh'))).mono
      simp only [hf,size_nil]
      rw [hf] at hs
      omega
    · have h5:=hg a s hf
      have hh':=RegisterStructured.select_cons 0 (seq (TreeFunction.split 0 2 (by decide)) H) _
        (env (encode (f a)) .nil (.cons (encode a) s)) (env (encode (g a)) .nil s) _
        .nil .nil (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh'))).mono
      simp only [hf,size_nil]
      rw [hf] at hs
      omega

def subProgram : Proc (K Reg) := seq (TreeFunction.split 1 0 (by decide))
  (seq (TreeArithmetic.sub 1 0 (by decide))
    (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1)))
def subCost (ab : ℕ×ℕ) : ℕ := 2*TreeFunction.size (nat ab.1)+
  9*(ab.1.bits.length+ab.2.bits.length)+4*TreeFunction.size (nat (ab.1-ab.2))+32
lemma subProgram_exec (a b : ℕ) (s : Data) (hab : b ≤ a) :
    Exec subProgram (encodeEnv (env (encode (a,b)) .nil s))
      (encodeEnv (env (nat (a-b)) .nil s)) (subCost (a,b)) := by
  have h1:=split10 (nat a) (nat b) .nil s
  have h2:=TreeArithmetic.sub_exec (env (nat b) (nat a) s) 1 0 (by decide) a b rfl rfl hab
  simp only [putPair,env_update0,env_update1] at h2
  have h3:=copy10 .nil (nat (a-b)) s
  have h4:=clear1 (nat (a-b)) (nat (a-b)) s
  apply (h1.seq (h2.seq (h3.seq h4))).mono
  simp only [size_nil,subCost]; omega

def subtract : Realizer (fun ab : ℕ×ℕ=>ab.1-ab.2) := by
  let Z : Realizer (fun _ : ℕ×ℕ=>0) := constant 0
  let P:=choosePartial (fun ab : ℕ×ℕ=>decide (ab.1<ab.2)) (fun _=>0) (fun ab=>ab.1-ab.2)
    less Z.program subProgram Z.cost subCost (fun a s _=>Z.correct a s)
    (fun a s h=>subProgram_exec a.1 a.2 s (by simpa only [decide_eq_false_iff_not,not_lt] using h))
  refine ⟨P.program,P.cost,?_⟩
  intro ab stack
  by_cases hlt : ab.1<ab.2
  · simpa [hlt,Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)] using P.correct ab stack
  · simpa [hlt] using P.correct ab stack
end MatchingFPRAS.TreeTyped

end OAI
