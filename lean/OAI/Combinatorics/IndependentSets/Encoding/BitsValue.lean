import Mathlib
import OAI.Combinatorics.IndependentSets.Model

namespace OAI

namespace LargeIndependentSets
namespace BinaryParser

def bitsValue : List Bool → ℕ
  | [] => 0
  | b::bs => Nat.bit b (bitsValue bs)

@[simp] lemma bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simp only [bitsValue,ih]

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false::rest => some ([],rest)
  | true::b::rest => do
      let (bs,tail) ← parseFrame rest
      return (b::bs,tail)
  | _ => none

@[simp] lemma parseFrame_encoded (bs tail : List Bool) :
    parseFrame (frame bs ++ tail) = some (bs,tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [frame,parseFrame,ih]

def parseName (b : List Bool) : Option (ℕ × List Bool) := do
  let (digits,tail) ← parseFrame b
  let n := bitsValue digits
  if digits = n.bits then some (n,tail) else none

@[simp] lemma parseName_encoded (n : ℕ) (tail : List Bool) :
    parseName (nameBits n ++ tail) = some (n,tail) := by
  simp [parseName,nameBits]

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign::b => do
      let (name,tail) ← parseName b
      return (⟨name,sign⟩,tail)
  | [] => none

@[simp] lemma parseLiteral_encoded (l : Literal) (tail : List Bool) :
    parseLiteral (literalBits l ++ tail) = some (l,tail) := by
  cases l
  simp [parseLiteral,literalBits]

def parseMany {α : Type} (parse : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0,b => some ([],b)
  | n+1,b => do
      let (a,b) ← parse b
      let (as,tail) ← parseMany parse n b
      return (a::as,tail)

lemma parseMany_encoded {α : Type} (parse : List Bool → Option (α × List Bool))
    (encode : α → List Bool) (P : α → Prop)
    (h : ∀ a, P a → ∀ tail, parse (encode a ++ tail) = some (a,tail))
    (as : List α) (has : ∀ a ∈ as, P a) (tail : List Bool) :
    parseMany parse as.length (as.flatMap encode ++ tail) = some (as,tail) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,parseMany,
      h a (has a (by simp)),bind,Option.bind]
    rw [ih (fun x hx => has x (by simp [hx]))]
    rfl

def parseClause (b : List Bool) : Option (List Literal × List Bool) := do
  let (n,b) ← parseName b
  if n ≤ 3 then parseMany parseLiteral n b else none

lemma parseClause_encoded (C : List Literal) (hC : C.length ≤ 3) (tail : List Bool) :
    parseClause (clauseBits C ++ tail) = some (C,tail) := by
  simp only [clauseBits,List.append_assoc,parseClause,parseName_encoded,bind,Option.bind,hC,ite_true]
  exact parseMany_encoded parseLiteral literalBits (fun _ => True)
    (fun l _ => parseLiteral_encoded l) C (by simp) tail

lemma clauses_length_le_bits (Cs : List (List Literal)) :
    Cs.length ≤ (Cs.flatMap clauseBits).length := by
  have hp (C : List Literal) : 1 ≤ (clauseBits C).length := by
    unfold clauseBits nameBits
    have h : ∀ b : List Bool, 1 ≤ (frame b).length := by
      intro b
      cases b <;> simp [frame]
    simpa only [List.length_append] using (h C.length.bits).trans (Nat.le_add_right _ _)
  induction Cs with
  | nil => simp
  | cons C Cs ih => simp only [List.length_cons,List.flatMap_cons,List.length_append]; have := hp C; omega

def core (input : List Bool) : Option Formula := do
  let (n,b) ← parseName input
  if n ≤ b.length then
    let (Cs,tail) ← parseMany parseClause n b
    if tail = [] then
      if h : ∀ C ∈ Cs, C.length ≤ 3 then some ⟨Cs,h⟩ else none
    else none
  else none

lemma core_encoded (F : Formula) : core (formulaBits F) = some F := by
  unfold core formulaBits
  rw [parseName_encoded]
  simp only [bind,Option.bind,clauses_length_le_bits,ite_true]
  have hm := parseMany_encoded parseClause clauseBits (fun C => C.length ≤ 3)
    parseClause_encoded F.clauses F.width []
  simp only [List.append_nil] at hm
  rw [hm]
  simp
  exact F.width

def decode (input : List Bool) : Formula :=
  match core input with
  | none => ⟨[],by simp⟩
  | some F => if formulaBits F = input then F else ⟨[],by simp⟩

@[simp] theorem decode_encoded (F : Formula) : decode (formulaBits F) = F := by
  simp [decode,core_encoded]

theorem decode_bits_bound (input : List Bool) :
    (formulaBits (decode input)).length ≤ input.length+1 := by
  unfold decode
  cases h : core input with
  | none => simp [formulaBits,nameBits,frame]
  | some F =>
    dsimp only
    split_ifs with he
    · simp only [he]; omega
    · simp [formulaBits,nameBits,frame]

end BinaryParser
end LargeIndependentSets

end OAI
