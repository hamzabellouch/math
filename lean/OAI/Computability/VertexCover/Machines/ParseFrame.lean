import Mathlib
import OAI.Computability.VertexCover.Encoding.BinaryEncoding
import OAI.Computability.VertexCover.Machines.Option

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

namespace VertexCover.Machine.FrameParser
open UniqueGames.BinaryEncoding

def next (q : Fin 3) (b : Bool) : Fin 3 :=
  if q=0 then (if b then 1 else 2) else if q=1 then 0 else 2

def state : Fin 3 → List Bool → Fin 3
  | q,[] => q
  | q,b::bs => state (next q b) bs

def trans (mode : Fin 3) (q : Fin 3) (b : Bool) : Fin 3 × List Bool :=
  (next q b, if (mode=0 ∧ q=1) ∨ (mode=1 ∧ q=2) then [b] else [])

def finish (mode : Fin 3) (q : Fin 3) : List Bool :=
  if mode=2 then [decide (q=2)] else []

def scan (mode : Fin 3) (q : Fin 3) (bs : List Bool) : List Bool :=
  Stream.output (trans mode) (finish mode) q bs

theorem flag (q : Fin 3) (bs : List Bool) : scan 2 q bs = [decide (state q bs=2)] := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih => exact ih (next q b)

theorem after_state (bs : List Bool) : state 2 bs = 2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa only [state,next,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,ite_false] using ih

theorem after_digits (bs : List Bool) : scan 0 2 bs = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [scan,Stream.output,trans,next,finish] using ih

theorem after_rest (bs : List Bool) : scan 1 2 bs = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [scan,Stream.output,trans,next,finish] using congrArg (List.cons b) ih

def parsed (bs : List Bool) : Option (List Bool × List Bool) :=
  if state 0 bs=2 then some (scan 0 0 bs,scan 1 0 bs) else none

theorem correct (bs : List Bool) : parsed bs = parseFrame bs := by
  induction bs using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> rfl
  | cons_cons a b bs ih _ =>
    cases a with
    | false =>
      change (if state 2 (b::bs)=2 then some (scan 0 2 (b::bs),scan 1 2 (b::bs)) else none) = some ([],b::bs)
      rw [after_state,after_digits,after_rest]
      rfl
    | true =>
      have hs : state 0 (true::b::bs) = state 0 bs := rfl
      have hd : scan 0 0 (true::b::bs) = b::scan 0 0 bs := rfl
      have hr : scan 1 0 (true::b::bs) = scan 1 0 bs := rfl
      simp only [parsed,hs,hd,hr,parseFrame]
      rw [← ih]
      by_cases h : state 0 bs=2 <;> simp [parsed,h]

noncomputable def scanner (mode : Fin 3) : Poly id id (scan mode 0) :=
  Stream.poly 0 (trans mode) (finish mode) 1
    (by intros; dsimp [trans]; split <;> simp)
    (by intros; dsimp [finish]; split <;> simp)

noncomputable def poly : Poly id (optionBits (prodBits id id)) parseFrame := by
  let valid : Poly id boolBits (fun bs => decide (state 0 bs=2)) := (scanner 2).encodeCongr id (fun _ => rfl) (fun bs => flag 0 bs)
  let pair := (scanner 0).pair (scanner 1)
  let somePair := pair.comp (Poly.some (prodBits id id))
  let c := valid.ite somePair (Poly.const id (optionBits (prodBits id id)) none)
  exact c.congr (fun bs => by
    have h : (if decide (state 0 bs=2) then some (scan 0 0 bs,scan 1 0 bs) else none) = parsed bs := by
      simp [parsed]
    exact h.trans (correct bs))

end VertexCover.Machine.FrameParser
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
