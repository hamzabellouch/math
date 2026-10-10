import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CollisionPhase

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def stemGerm (g : Germ) (b : Bool) : Germ := (g.1,unusedSlot g b)

def reverseLoopGerm (g : Germ) (b : Bool) : Germ := (g.1,outgoingSlot g b)

@[simp] theorem stem_forward (g : Germ) (b : Bool) :
    advance (stemGerm g b) (!b) = advance g b := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [stemGerm,unusedSlot,advance,outgoingSlot]

@[simp] theorem stem_reverse (g : Germ) (b : Bool) :
    advance (stemGerm g b) b = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [stemGerm,unusedSlot,advance,outgoingSlot,reverseGerm]

@[simp] theorem reverseLoop_advance (g : Germ) (b : Bool) :
    advance (reverseLoopGerm g b) (!b) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,advance,outgoingSlot,reverseGerm]

@[simp] theorem reverseLoop_reverseLoop (g : Germ) (b : Bool) :
    reverseLoopGerm (reverseLoopGerm g b) (!b) = g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,outgoingSlot]

@[simp] theorem reverseLoop_stem (g : Germ) (b : Bool) :
    stemGerm (reverseLoopGerm g b) (!b) = stemGerm g b := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,stemGerm,unusedSlot,outgoingSlot]

@[simp] theorem reverseGerm_advance_eq (g : Germ) (b : Bool) :
    reverseGerm (advance g b) = reverseLoopGerm g b := by
  simp [reverseGerm,advance,reverseLoopGerm]

@[simp] theorem stem_forward_trace (g : Germ) (b : Bool) (w : List Bool) :
    traced (stemGerm g b) ((!b) :: w) = traced g (b :: w) := by
  change g.1 :: traced (advance (stemGerm g b) (!b)) w = _
  rw [stem_forward]
  rfl

@[simp] theorem stem_forward_terminal (g : Germ) (b : Bool) (w : List Bool) :
    terminalGerm (stemGerm g b) ((!b) :: w) = terminalGerm g (b :: w) := by
  simp [terminalGerm]

theorem stem_reverse_trace (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    traced (stemGerm g b) (b :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse := by
  have hr := traced_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  change g.1 :: traced (advance (stemGerm g b) b) (reverseTurns w) = _
  rw [stem_reverse,hr]

theorem reverse_loop_terminal (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    terminalGerm (reverseLoopGerm g b) ((!b) :: reverseTurns w) =
      reverseLoopGerm g b := by
  have hr := terminalGerm_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  simpa only [terminalGerm, reverseLoop_advance, reverseGerm_advance_eq] using hr

theorem reverse_loop_trace (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    traced (reverseLoopGerm g b) ((!b) :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse := by
  have hr := traced_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  change g.1 :: traced (advance (reverseLoopGerm g b) (!b)) (reverseTurns w) = _
  rw [reverseLoop_advance,hr]

theorem reverse_loop_nodup (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) (hN : (traced g (b :: w)).Nodup) :
    (traced (reverseLoopGerm g b) ((!b) :: reverseTurns w)).Nodup := by
  rw [reverse_loop_trace g b w hc]
  simpa [traced] using hN

@[simp] theorem dartFlow_reverse (g : Germ) : dartFlow (reverseGerm g) = -dartFlow g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [dartFlow,edgeOf,dartSign,reverseGerm,neighbor]

@[simp] theorem reverseLoop_outgoing (g : Germ) (b : Bool) :
    ((reverseLoopGerm g b).1,outgoingSlot (reverseLoopGerm g b) (!b)) = g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,outgoingSlot]

theorem wordFlow_reverse (g : Germ) (w : List Bool) :
    wordFlow (reverseGerm (terminalGerm g w)) (reverseTurns w) =
      -wordFlow g w + dartFlow g - dartFlow (terminalGerm g w) := by
  induction w generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b w ih =>
      simp only [terminalGerm,reverseTurns_cons,wordFlow_append,wordFlow,ih]
      rw [terminalGerm_reverse]
      simp only [reverseGerm_advance_eq,reverseLoop_outgoing,add_zero]
      have hd : dartFlow (advance g b) = -dartFlow (g.1,outgoingSlot g b) := by
        exact dartFlow_reverse (g.1,outgoingSlot g b)
      rw [hd]
      abel

theorem reverse_loop_flow (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    wordFlow (reverseLoopGerm g b) ((!b) :: reverseTurns w) = -wordFlow g (b :: w) := by
  have hr := wordFlow_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  simp only [wordFlow,reverseLoop_outgoing,reverseLoop_advance]
  rw [hr]
  have hd : dartFlow (advance g b) = -dartFlow (g.1,outgoingSlot g b) :=
    dartFlow_reverse (g.1,outgoingSlot g b)
  rw [hd]
  abel

end PolynomialVacuumBridge.Corridor

end

end OAI
