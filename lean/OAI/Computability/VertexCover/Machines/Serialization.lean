import Mathlib
import OAI.Computability.VertexCover.Reduction.Soundness
import OAI.Computability.VertexCover.Machines.DenseParse
import OAI.Computability.VertexCover.Machines.ParseFormula

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
open UniqueGames.Foundations.Complexity

noncomputable def Poly.rawFlatten : Poly (listBits (id : List Bool → List Bool)) id List.flatten := by
  let c := Poly.foldGrowing id id ([] : List Bool) Poly.append 1 (by
    intro out xs
    simp only [id_eq,List.length_append,Nat.one_mul]
    omega)
  let input := (Poly.const (listBits id) id ([] : List Bool)).pair (Poly.identity (listBits id))
  exact (input.comp c).congr (fun xs => by
    change xs.foldl (fun out xs => out++xs) [] = xs.flatten
    have h (xs : List (List Bool)) (out : List Bool) :
        xs.foldl (fun out xs => out++xs) out = out++xs.flatten := by
      induction xs generalizing out with
      | nil => simp
      | cons a xs ih => simp [List.foldl_cons,ih,List.append_assoc]
    simpa using h xs [])

noncomputable def Poly.word : Poly natBits id encodeWord := by
  let raw : Poly natBits id natBits :=
    (Poly.identity natBits).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact ((raw.pair (Poly.const natBits id [false])).comp Poly.append).congr (fun _ => rfl)

noncomputable def Poly.words : Poly (listBits natBits) id encodeWords := by
  let c := (Poly.listMap natBits id 0 [] Poly.word).comp Poly.rawFlatten
  refine c.congr ?_
  intro xs
  change (xs.map encodeWord).flatten = encodeWords xs
  induction xs with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons,List.flatten_cons,encodeWords,ih]

namespace FormulaParser

def literalDataWords (p : Bool × ℕ) : List ℕ := [p.2,if p.1 then 1 else 0]
def clauseDataWords (p : Triple (Bool × ℕ)) : List ℕ :=
  literalDataWords p.1.1 ++ literalDataWords p.1.2 ++ literalDataWords p.2

def formulaDataWords (F : FormulaData) : List ℕ :=
  [F.1,F.2.length] ++ F.2.flatMap clauseDataWords

noncomputable def literalWordsPoly : Poly unaryLiteralCode (listBits natBits) literalDataWords := by
  let sign := (Poly.fst boolBits natBits).comp
    (Poly.finite boolBits natBits (by
      intro a b h; exact List.singleton_injective h) (fun b : Bool => if b then 1 else 0))
  let last := (sign.pair (Poly.const unaryLiteralCode (listBits natBits) [])).comp (Poly.listCons natBits)
  exact (((Poly.snd boolBits natBits).pair last).comp (Poly.listCons natBits)).congr (fun _ => rfl)

noncomputable def clauseWordsPoly : Poly unaryClauseCode (listBits natBits) clauseDataWords := by
  let ab := Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode
  let a := (ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)).comp literalWordsPoly
  let b := (ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)).comp literalWordsPoly
  let c := (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode).comp literalWordsPoly
  exact ((((a.pair b).comp (Poly.listAppend natBits 0)).pair c).comp
    (Poly.listAppend natBits 0)).congr (fun _ => rfl)

noncomputable def formulaWordsPoly : Poly dataCode (listBits natBits) formulaDataWords := by
  let n := Poly.fst natBits (listBits unaryClauseCode)
  let cs := Poly.snd natBits (listBits unaryClauseCode)
  let len := cs.comp (Poly.listLength unaryClauseCode (((false,0),(false,0)),(false,0)))
  let last := (len.pair (Poly.const dataCode (listBits natBits) [])).comp (Poly.listCons natBits)
  let first := (n.pair last).comp (Poly.listCons natBits)
  let body := cs.comp (Poly.listFlatMap unaryClauseCode natBits
    (((false,0),(false,0)),(false,0)) 0 clauseWordsPoly)
  exact ((first.pair body).comp (Poly.listAppend natBits 0)).congr (fun _ => rfl)

theorem formulaDataWords_target (F : UniqueGames.Foundations.Target.Formula) :
    formulaDataWords (targetData F) = formulaWords F := by
  simp only [formulaDataWords,targetData,List.length_map,formulaWords,List.flatMap_map]
  rfl

noncomputable def serializePoly : Poly targetCode formulaBits id :=
  (formulaWordsPoly.comp Poly.words).encodeCongr targetData (fun _ => rfl) (fun F => by
    change encodeWords (formulaDataWords (targetData F)) = formulaBits F
    rw [formulaDataWords_target]; rfl)

noncomputable def rawDensePoly : Poly id formulaBits
    (fun bs => UniqueGames.BinaryFormula.dense (VertexCover.ClauseProjection.inputFormula bs)) :=
  (inputFormulaPoly.comp densePoly).comp serializePoly
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
