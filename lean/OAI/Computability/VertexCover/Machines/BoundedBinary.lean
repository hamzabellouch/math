import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringMoment
import OAI.Computability.VertexCover.Machines.ListIndex

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
open UniqueGames.BinaryEncoding

noncomputable def Poly.natMin : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => min p.1 p.2) :=
  (Poly.natLE.ite (Poly.fst natBits natBits) (Poly.snd natBits natBits)).congr (by
    intro ⟨a,b⟩
    by_cases h : a ≤ b <;> simp [h,Nat.min_def])

namespace CappedBinary
abbrev State := ℕ × ℕ
abbrev enc : State → List Bool := prodBits natBits natBits

def step (p : State × Bool) : State :=
  (p.1.1,min p.1.1 (Nat.bit p.2 p.1.2))

noncomputable def stepPoly : Poly (prodBits enc boolBits) enc step := by
  let s := Poly.fst enc boolBits
  let B := s.comp (Poly.fst natBits natBits)
  let v := s.comp (Poly.snd natBits natBits)
  let b := Poly.snd enc boolBits
  let twice := (v.pair v).comp Poly.natAdd
  let val := b.ite (twice.comp Poly.natSucc) twice
  let cap := (B.pair val).comp Poly.natMin
  exact (B.pair cap).congr (fun ⟨⟨B,v⟩,b⟩ => by cases b <;> simp [step,Nat.bit,two_mul])

theorem fold_bound (xs : List Bool) (B v : ℕ) :
    (xs.foldl (fun s b => step (s,b)) (B,v)).1 = B ∧
    (xs.foldl (fun s b => step (s,b)) (B,v)).2 ≤ max B v := by
  induction xs generalizing v with
  | nil => exact ⟨rfl, Nat.le_max_right _ _⟩
  | cons b bs ih =>
    obtain ⟨h₁,h₂⟩ := ih (min B (Nat.bit b v))
    refine ⟨h₁, h₂.trans ?_⟩
    exact (max_le (le_refl _) (Nat.min_le_left _ _)).trans (Nat.le_max_left _ _)

noncomputable def foldPoly : Poly (prodBits enc (listBits boolBits)) enc
    (fun p : State × List Bool => p.2.foldl (fun s b => step (s,b)) p.1) := by
  refine Poly.fold boolBits enc false stepPoly (3*Polynomial.X+3) ?_
  intro ⟨B,v⟩ xs pre suf h
  have hh := fold_bound pre B v
  have hs := listBits_append_length boolBits pre suf
  rw [h] at hs
  have hp := listBits_length_pos boolBits pre
  simp only [prodBits,enc,pairBits_length,natBits_length,hh.1,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

theorem min_bit (B n : ℕ) (b : Bool) :
    min B (Nat.bit b (min B n)) = min B (Nat.bit b n) := by
  cases b <;> simp only [Nat.bit,Bool.cond_false,Bool.cond_true] <;> omega

theorem foldr (bs : List Bool) (B : ℕ) :
    bs.foldr (fun b s => step (s,b)) (B,0) = (B,min B (bitsValue bs)) := by
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    rw [List.foldr_cons,ih]
    simp only [step,bitsValue,min_bit]

end CappedBinary

noncomputable def Poly.decodeBounded : Poly (prodBits natBits id) natBits
    (fun p : ℕ × List Bool => min p.1 (bitsValue p.2)) := by
  let B := Poly.fst natBits id
  let bs := (Poly.snd natBits id).comp Poly.rawToList
  let input := (B.pair (Poly.const (prodBits natBits id) natBits 0)).pair
    (bs.comp (Poly.listReverse boolBits false))
  let c := (input.comp CappedBinary.foldPoly).comp (Poly.snd natBits natBits)
  refine c.congr ?_
  intro ⟨B,bs⟩
  change (bs.reverse.foldl (fun s b => CappedBinary.step (s,b)) (B,0)).2 = _
  rw [List.foldl_reverse,CappedBinary.foldr]

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
