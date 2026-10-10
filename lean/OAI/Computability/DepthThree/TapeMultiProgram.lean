import OAI.Computability.DepthThree.TapeEncoding
import OAI.Computability.DepthThree.TapeWord
import OAI.Computability.DepthThree.MultiTapeMachine

namespace OAI

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7

namespace DepthThreeLowerBound

open Turing

abbrev TapeHeads := TapeRegister → TapeSymbol
abbrev TapeMoves := TapeRegister → HeadMove
abbrev TapeTapes := TapeRegister → Tape TapeSymbol
abbrev TapeMultiCfg (Q : Type uDepth1) := MultiTapeCfg TapeRegister TapeSymbol Q
abbrev TapeMultiProgram (Q : Type uDepth2) :=
  Q → TapeHeads → Option (Q × TapeHeads × TapeMoves)

def wordTape (bits : List Bool) : Tape TapeSymbol :=
  Tape.mk₁ (cleanAtom .home :: (encodeInput bits ++ [cleanAtom .endMark]))

def cursorTape (before after : List Bool) : Tape TapeSymbol :=
  Tape.mk₂ ((encodeInput before).reverse ++ [cleanAtom .home])
    (encodeInput after ++ [cleanAtom .endMark])

@[simp] theorem wordTape_head (bits : List Bool) :
    (wordTape bits).head = cleanAtom .home := rfl

@[simp] theorem cursorTape_head_cons (before after : List Bool) (b : Bool) :
    (cursorTape before (b :: after)).head = rawInputSymbol b := rfl

@[simp] theorem cursorTape_head_nil (before : List Bool) :
    (cursorTape before []).head = cleanAtom .endMark := rfl

@[simp] theorem wordTape_right (bits : List Bool) :
    (wordTape bits).move Dir.right = cursorTape [] bits := rfl

theorem cursorTape_right (before after : List Bool) (b : Bool) :
    (cursorTape before (b :: after)).move Dir.right =
      cursorTape (before ++ [b]) after := by
  simp only [cursorTape, encodeInput, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, TapeWord.move_right_mk₂_cons]

namespace TapeMultiProgram

def step {Q : Type uDepth3} (P : TapeMultiProgram Q) : TapeMultiCfg Q → Option (TapeMultiCfg Q) :=
  multiTapeStep P

def cfg {Q : Type uDepth4} (q : Q) (T : TapeTapes) : TapeMultiCfg Q := ⟨q, T⟩

def heads (T : TapeTapes) : TapeHeads := fun r => (T r).head

def stayMoves : TapeMoves := fun _ => .stay

def moveOnly (r : TapeRegister) (d : HeadMove) : TapeMoves :=
  Function.update stayMoves r d

def writeOnly (r : TapeRegister) (symbol : TapeSymbol) (h : TapeHeads) : TapeHeads :=
  Function.update h r symbol

def jump {Q : Type uDepth5} (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) := some (q, h, stayMoves)

def move {Q : Type uDepth6} (r : TapeRegister) (d : HeadMove) (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) := some (q, h, moveOnly r d)

def writeMove {Q : Type uDepth7} (r : TapeRegister) (symbol : TapeSymbol)
    (d : HeadMove) (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) :=
  some (q, writeOnly r symbol h, moveOnly r d)

def isAtom (a : TapeAtom) (r : TapeRegister) (h : TapeHeads) : Bool :=
  decide ((h r).1 = a)

def machine {Q : Type} [Fintype Q] (P : TapeMultiProgram Q)
    (initial : Q) (accept : Q → Bool) : FiniteMultiTapeMachine where
  K := TapeRegister
  inputTape := TapeRegister.input
  Γ := TapeSymbol
  Q := Q
  initialState := initial
  inputSymbol := rawInputSymbol
  input_injective := rawInputSymbol_injective
  input_ne_blank := by simpa only [default_tapeSymbol] using rawInputSymbol_ne_blank
  code := P
  accept := accept

end TapeMultiProgram
end DepthThreeLowerBound

end OAI
