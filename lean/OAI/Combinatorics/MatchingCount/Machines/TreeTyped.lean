import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeNumberOps
import OAI.Combinatorics.MatchingCount.Machines.TreeFunction

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

class Codec (A : Type) where
  encode : A → Data
export Codec (encode)
instance : Codec Data := ⟨id⟩
instance : Codec ℕ := ⟨nat⟩
instance : Codec Bool := ⟨bit⟩
instance {A B : Type} [Codec A] [Codec B] : Codec (A×B) := ⟨fun x=>.cons (encode x.1) (encode x.2)⟩
instance {A : Type} [Codec A] : Codec (List A) := ⟨fun x=>ofList (x.map encode)⟩
@[simp] lemma encode_prod {A B : Type} [Codec A] [Codec B] (a : A) (b : B) :
    encode (a,b)=.cons (encode a) (encode b) := rfl
@[simp] lemma encode_list_nil {A : Type} [Codec A] : encode ([] : List A)=.nil := rfl
@[simp] lemma encode_list_cons {A : Type} [Codec A] (a : A) (as : List A) :
    encode (a::as)=.cons (encode a) (encode as) := rfl

def Realizes {A B : Type} [Codec A] [Codec B] (P : Proc (K Reg)) (f : A → B) (t : A → ℕ) : Prop :=
  ∀ a s,Exec P (encodeEnv (env (encode a) .nil s)) (encodeEnv (env (encode (f a)) .nil s)) (t a)
structure Realizer {A B : Type} [Codec A] [Codec B] (f : A → B) where
  program : Proc (K Reg)
  cost : A → ℕ
  correct : Realizes program f cost

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def composition {f : A → B} {g : B → C} (F : Realizer f) (G : Realizer g) : Realizer (g ∘ f) :=
  ⟨seq F.program G.program,fun a=>F.cost a+G.cost (f a),fun a s=>(F.correct a s).seq (G.correct (f a) s)⟩

def pair {f : A → B} {g : A → C} (F : Realizer f) (G : Realizer g) : Realizer (fun a=>(f a,g a)) where
  program := TreeFunction.pair F.program G.program
  cost := fun a=>F.cost a+G.cost a+11*TreeFunction.size (encode a)+6*TreeFunction.size (encode (f a))+31
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split12 (encode (f a)) .nil (encode a) s
    have h5:=cons02 (encode (f a)) (encode a) s
    have h6:=copy10 .nil (encode a) (.cons (encode (f a)) s)
    have h7:=clear1 (encode a) (encode a) (.cons (encode (f a)) s)
    have h8:=G.correct a (.cons (encode (f a)) s)
    have h9:=split12 (encode (g a)) .nil (encode (f a)) s
    have h10:=cons10 (encode (g a)) (encode (f a)) s
    apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq h10))))))))).mono
    simp only [size_nil]
    omega

def identity : Realizer (id : A → A) :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def first : Realizer (Prod.fst : A×B → A) where
  program := seq (TreeFunction.split 1 0 (by decide))
    (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1))
  cost := fun ab=>6*TreeFunction.size (encode ab.1)+TreeFunction.size (encode ab.2)+11
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (encode a) (encode b) .nil s
    have h2:=copy10 (encode b) (encode a) s
    have h3:=clear1 (encode a) (encode a) s
    apply (h1.seq (h2.seq h3)).mono
    simp only [size_nil]; omega

def second : Realizer (Prod.snd : A×B → B) where
  program := seq (TreeFunction.split 1 0 (by decide)) (TreeFunction.clear 1)
  cost := fun ab=>3*TreeFunction.size (encode ab.1)+7
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (encode a) (encode b) .nil s
    have h2:=clear1 (encode b) (encode a) s
    apply (h1.seq h2).mono
    simp only [size_nil]; omega

def add : Realizer (fun ab : ℕ×ℕ=>ab.1+ab.2) where
  program := seq (TreeFunction.split 1 0 (by decide)) (TreeArithmetic.add 0 1 (by decide))
  cost := fun ab=>2*TreeFunction.size (nat ab.1)+5+9*(ab.1.bits.length+ab.2.bits.length)+20
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (nat a) (nat b) .nil s
    have h2:=TreeArithmetic.add_exec (env (nat b) (nat a) s) 0 1 (by decide) b a rfl rfl
    rw [putPair,env_update0,env_update1,Nat.add_comm b a] at h2
    apply (h1.seq h2).mono
    simp only [size_nil]
    omega
end MatchingFPRAS.TreeTyped

end OAI
