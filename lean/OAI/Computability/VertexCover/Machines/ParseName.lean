import Mathlib
import OAI.Computability.VertexCover.Basic
import OAI.Computability.VertexCover.PCP.PoweringMoment
import OAI.Computability.VertexCover.Machines.Option
import OAI.Computability.VertexCover.Machines.ParseFrame

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

namespace VertexCover.Machine.NameParser
open UniqueGames.BinaryEncoding

def canonical : List Bool → Bool
  | [] => true
  | [b] => b
  | _::b::bs => canonical (b::bs)

theorem canonical_iff (bs : List Bool) : canonical bs = true ↔ (bitsValue bs).bits = bs := by
  induction bs with
  | nil => simp [canonical,bitsValue]
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> simp [canonical,bitsValue,Nat.bit]
    | cons c cs =>
      change canonical (c::cs)=true ↔ (bitsValue (b::c::cs)).bits=b::c::cs
      constructor
      · intro h
        have hc := ih.mp h
        have hn : bitsValue (c::cs) ≠ 0 := by
          intro hz
          rw [hz,Nat.zero_bits] at hc
          contradiction
        change (Nat.bit b (bitsValue (c::cs))).bits = _
        rw [Nat.bits_append_bit _ _ (fun hz => False.elim (hn hz)),hc]
      · intro h
        apply ih.mpr
        have ht := congrArg List.tail h
        simpa only [bitsValue,← Nat.div2_bits_eq_tail,Nat.div2_bit,List.tail_cons] using ht

def trans (_ : Bool) (b : Bool) : Bool × List Bool := (b,[])

theorem canon_scan (q : Bool) (b : Bool) (bs : List Bool) :
    Stream.output trans (fun q => [q]) q (b::bs) = [canonical (b::bs)] := by
  induction bs generalizing q b with
  | nil => rfl
  | cons c cs ih => exact ih b c

noncomputable def canonicalPoly : Poly id boolBits canonical :=
  (Stream.poly true trans (fun q => [q]) 1 (by intros; exact Nat.zero_le _) (by intros; rfl)).realizes
    (fun bs => by cases bs with | nil => rfl | cons b bs => exact canon_scan true b bs)

def core (p : List Bool × List Bool) : Option (ℕ × List Bool) :=
  if p.1=(bitsValue p.1).bits then some (bitsValue p.1,p.2) else none

noncomputable def corePoly : Poly (prodBits id id) (optionBits (prodBits Nat.bits id)) core := by
  let test := (Poly.fst id id).comp canonicalPoly
  let c := test.ite (Poly.some (prodBits id id))
    (Poly.const (prodBits id id) (optionBits (prodBits id id)) none)
  refine c.encodeCongr id (fun _ => rfl) ?_
  intro ⟨digits,rest⟩
  by_cases h : canonical digits=true
  · have hc := (canonical_iff digits).mp h
    simp [core,h,hc,optionBits,prodBits]
  · have hc : digits ≠ (bitsValue digits).bits := by
      intro he
      exact h ((canonical_iff digits).mpr he.symm)
    simp [core,h,hc,optionBits]

noncomputable def poly : Poly id (optionBits (prodBits Nat.bits id)) parseName :=
  (FrameParser.poly.comp (Poly.optionBind (prodBits id id) (prodBits Nat.bits id) ([],[]) corePoly)).congr (fun _ => rfl)

end VertexCover.Machine.NameParser
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
