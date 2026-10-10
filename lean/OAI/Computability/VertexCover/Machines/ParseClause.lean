import Mathlib
import OAI.Computability.VertexCover.Machines.Lists
import OAI.Computability.VertexCover.Machines.ParseName

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine

noncomputable def Poly.optionMapWith {α β γ : Type} (ea : α → List Bool)
    (eb : β → List Bool) (ec : γ → List Bool) (b₀ : β)
    {f : α × β → γ} (cf : Poly (prodBits ea eb) ec f) :
    Poly (prodBits ea (optionBits eb)) (optionBits ec)
      (fun p : α × Option β => p.2.map (fun b => f (p.1,b))) := by
  let a := Poly.fst ea (optionBits eb)
  let b := Poly.snd ea (optionBits eb)
  let test := b.comp (Poly.isSome eb)
  let result := ((a.pair (b.comp (Poly.getD eb b₀))).comp cf).comp (Poly.some ec)
  exact (test.ite result (Poly.const _ (optionBits ec) none)).congr (fun ⟨a,b⟩ => by cases b <;> rfl)

namespace Parser
abbrev P (α : Type) := List Bool → Option (α × List Bool)

def seq {α β : Type} (pa : P α) (pb : P β) : P (α × β) := fun input => do
  let (a,rest) ← pa input
  let (b,rest) ← pb rest
  return ((a,b),rest)

noncomputable def seqPoly {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {pa : P α} {pb : P β}
    (ca : Poly id (optionBits (prodBits ea id)) pa)
    (cb : Poly id (optionBits (prodBits eb id)) pb) :
    Poly id (optionBits (prodBits (prodBits ea eb) id)) (seq pa pb) := by
  let e := prodBits eb id
  let a := Poly.fst ea e
  let b := (Poly.snd ea e).comp (Poly.fst eb id)
  let rest := (Poly.snd ea e).comp (Poly.snd eb id)
  let collect := (a.pair b).pair rest
  let step := (((Poly.fst ea id).pair ((Poly.snd ea id).comp cb)).comp
    (Poly.optionMapWith ea e (prodBits (prodBits ea eb) id) (b₀,[]) collect))
  exact (ca.comp (Poly.optionBind (prodBits ea id) (prodBits (prodBits ea eb) id)
    (a₀,[]) step)).congr (fun input => by
      cases ha : pa input with
      | none => simp [seq,ha]
      | some a => cases hb : pb a.2 <;> simp [seq,ha,hb])
end Parser

namespace FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

def literalCode (l : Literal) : List Bool := prodBits boolBits Nat.bits (l.positive,l.name)
def clauseCode (clause : Clause) : List Bool :=
  prodBits (prodBits literalCode literalCode) literalCode ((clause[0],clause[1]),clause[2])
def formulaCode (F : Formula) : List Bool := listBits clauseCode F.clauses

def literalDefault : Literal := ⟨0,false⟩
def clauseDefault : Clause := #v[literalDefault,literalDefault,literalDefault]

noncomputable def literalPoly : Poly id (optionBits (prodBits literalCode id)) parseLiteral := by
  let e := prodBits Nat.bits id
  let sign := Poly.fst boolBits e
  let n := (Poly.snd boolBits e).comp (Poly.fst Nat.bits id)
  let rest := (Poly.snd boolBits e).comp (Poly.snd Nat.bits id)
  let mkLit : Poly (prodBits boolBits e) literalCode
      (fun p : Bool × (ℕ × List Bool) => ⟨p.2.1,p.1⟩) :=
    (sign.pair n).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  let collect := mkLit.pair rest
  let parsed := ((Poly.headD false).pair (Poly.tail.comp NameParser.poly)).comp
    (Poly.optionMapWith boolBits e (prodBits literalCode id) (0,[]) collect)
  exact (Poly.isEmpty.ite (Poly.const id (optionBits (prodBits literalCode id)) none) parsed).congr (fun input => by
      cases input with
      | nil => rfl
      | cons b bs => cases h : parseName bs <;> simp [parseLiteral,h])

noncomputable def clausePoly : Poly id (optionBits (prodBits clauseCode id)) parseClause := by
  let c₁ := Parser.seqPoly literalCode literalCode literalDefault literalDefault literalPoly literalPoly
  let c₂ := Parser.seqPoly (prodBits literalCode literalCode) literalCode
    (literalDefault,literalDefault) literalDefault c₁ literalPoly
  refine c₂.encodeCongr id (fun _ => rfl) ?_
  intro input
  simp only [Parser.seq,parseClause,id_eq]
  cases h₁ : parseLiteral input with
  | none => rfl
  | some a =>
    rcases a with ⟨a,rest⟩
    cases h₂ : parseLiteral rest with
    | none => simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, h₂, Option.bind_none, optionBits]
    | some b =>
      rcases b with ⟨b,rest₂⟩
      cases h₃ : parseLiteral rest₂ with
      | none => simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, h₂, h₃, Option.bind_none, optionBits]
      | some c =>
        rcases c with ⟨c,rest₃⟩
        simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, h₂, h₃]
        rfl

end FormulaParser
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
