import Mathlib
import OAI.Computability.VertexCover.Basic
import OAI.Computability.VertexCover.Machines.ListGrowing

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
namespace Index
variable {α : Type} [BEq α]
def step (p : (α × ℕ) × α) : α × ℕ :=
  (p.1.1,if p.2 == p.1.1 then 0 else p.1.2+1)

theorem foldr (xs : List α) (a : α) :
    xs.foldr (fun x s => step (s,x)) (a,0) = (a,xs.idxOf a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons,ih]
    simp only [step,List.idxOf_cons]

noncomputable def poly (ea : α → List Bool)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits (prodBits ea natBits) ea) (prodBits ea natBits) step := by
  let s := Poly.fst (prodBits ea natBits) ea
  let a := s.comp (Poly.fst ea natBits)
  let n := s.comp (Poly.snd ea natBits)
  let x := Poly.snd (prodBits ea natBits) ea
  let test := (x.pair a).comp ce
  exact (a.pair (test.ite (Poly.const _ natBits 0) (n.comp Poly.natSucc))).congr (fun _ => rfl)
end Index

noncomputable def Poly.listIdxOf {α : Type} [BEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits ea (listBits ea)) natBits (fun p : α × List α => p.2.idxOf p.1) := by
  let e := prodBits ea natBits
  let c := Poly.foldGrowing ea e a₀ (Index.poly ea ce) 1 (by
    intro ⟨a,n⟩ x
    simp only [Index.step,e,prodBits,pairBits_length,natBits_length]
    split <;> omega)
  let input := ((Poly.fst ea (listBits ea)).pair (Poly.const _ natBits 0)).pair
    ((Poly.snd ea (listBits ea)).comp (Poly.listReverse ea a₀))
  exact ((input.comp c).comp (Poly.snd ea natBits)).congr (fun ⟨a,xs⟩ => by
    change (xs.reverse.foldl (fun s x => Index.step (s,x)) (a,0)).2 = xs.idxOf a
    rw [List.foldl_reverse,Index.foldr])

noncomputable def Poly.bitsNatEq : Poly (prodBits Nat.bits Nat.bits) boolBits
    (fun p : ℕ × ℕ => p.1 == p.2) :=
  Poly.rawEq.encodeCongr (fun p => (p.1.bits,p.2.bits)) (fun _ => rfl) (fun p => by
    have he : p.1.bits=p.2.bits ↔ p.1=p.2 := by
      constructor
      · intro h
        have hh := congrArg UniqueGames.BinaryEncoding.bitsValue h
        simpa only [UniqueGames.BinaryEncoding.bitsValue_bits] using hh
      · exact congrArg Nat.bits
    simp only [he]
    apply congrArg boolBits
    apply Bool.eq_iff_iff.mpr
    simp)

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
