import OAI.Computability.MatchingCount.LengthRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
class Coding (α : Type) where
  encode : α → List Bool
export Coding (encode)
instance : Coding ℕ := ⟨unary⟩
instance : Coding Bool := ⟨fun b => [b]⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α×β) :=
  ⟨fun z => pairBits (encode z.1) (encode z.2)⟩

def listCode {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::l => pairBits (ea a) (listCode ea l)
instance {α : Type} [Coding α] : Coding (List α) := ⟨listCode encode⟩

@[simp] lemma encode_nat (n : ℕ) : encode n=unary n := rfl
@[simp] lemma encode_bool (b : Bool) : encode b=[b] := rfl
@[simp] lemma encode_pair {α β : Type} [Coding α] [Coding β] (a : α) (b : β) :
    encode (a,b)=pairBits (encode a) (encode b) := rfl
@[simp] lemma encode_prod {α β : Type} [Coding α] [Coding β] (z : α×β) :
    encode z=pairBits (encode z.1) (encode z.2) := rfl

@[simp] lemma code_nil {α : Type} [Coding α] : encode ([]:List α)=[] := rfl
@[simp] lemma code_cons {α : Type} [Coding α] (a : α) (l : List α) :
    encode (a::l)=pairBits (encode a) (encode l) := rfl

lemma pairBits_append (x y z : List Bool) : pairBits x (y++z)=pairBits x y++z := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [pairBits,List.cons_append,Function.comp_apply] using congrArg (List.cons false ∘ List.cons b) ih

lemma code_append {α : Type} [Coding α] (l m : List α) : encode (l++m)=encode l++encode m := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,code_cons,ih,pairBits_append]

lemma list_length_le_code {α : Type} [Coding α] (l : List α) : l.length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons,code_cons,pairBits_length]; omega

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (Routine encode encode f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def routine {f : α → β} (h : Poly f) : Routine encode encode f := Classical.choice h

@[fun_prop] theorem identity : Poly (fun a : α => a) := ⟨Routine.identity encode⟩
@[fun_prop] theorem constant (b : β) : Poly (fun _ : α => b) := ⟨Routine.constant encode encode b⟩
@[fun_prop] theorem comp (f : β → γ) (g : α → β) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f (g a)) := ⟨hg.routine.comp hf.routine⟩
@[fun_prop] theorem pair (f : α → β) (g : α → γ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => (f a,g a)) := ⟨hf.routine.pair hg.routine⟩
@[fun_prop] theorem first (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).1) :=
  ⟨hf.routine.comp (Routine.first encode encode)⟩
@[fun_prop] theorem second (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).2) :=
  ⟨hf.routine.comp (Routine.second encode encode)⟩

@[fun_prop] theorem cond (b : α → Bool) (f g : α → β) (hb : Poly b) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => if b a then g a else f a) := by
  let p := (hb.routine.pair (Routine.identity encode)).comp (hf.routine.select hg.routine)
  exact ⟨p⟩

@[fun_prop] theorem codeLength : Poly (fun a : α => (encode a).length) := ⟨Routine.codeLength encode⟩

theorem boundedIterate (f : α → α) (hf : Poly f) (P : Polynomial ℕ)
    (h : ∀ (z : ℕ×α) j,j≤z.1 → (encode (f^[j] z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : ℕ×α => f^[z.1] z.2) :=
  ⟨hf.routine.boundedIterate Prod.fst Prod.snd P h⟩

theorem congr {f g : α → β} (hf : Poly f) (h : ∀ a,f a=g a) : Poly g := by
  have he : f=g := funext h
  rwa [←he]

end Poly
end BinaryMatching.StackCode
end

end OAI
