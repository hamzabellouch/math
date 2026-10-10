import OAI.Computability.DepthThree.TapeWord

namespace OAI

universe uDepth1

namespace DepthThreeLowerBound

namespace TapeWord

open Turing

variable {Γ : Type uDepth1} [Inhabited Γ]

@[simp] theorem move_left_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ (a :: L) R).move Dir.left = Tape.mk₂ L (a :: R) :=
  Tape.move_left_mk' (ListBlank.mk (a :: L)) (ListBlank.mk R)

theorem move_left_iterate_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.left)^[«prefix».length] (Tape.mk₂ («prefix» ++ L) R) =
      Tape.mk₂ L («prefix».reverse ++ R) := by
  induction «prefix» generalizing R with
  | nil => rfl
  | cons a «prefix» ih =>
    rw [List.length_cons, List.cons_append, Function.iterate_succ_apply,
      move_left_mk₂_cons]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append] using ih (a :: R)

theorem move_left_iterate_reverse_mk₂ («prefix» L R : List Γ) :
    (Tape.move Dir.left)^[«prefix».length] (Tape.mk₂ («prefix».reverse ++ L) R) =
      Tape.mk₂ L («prefix» ++ R) := by
  simpa only [List.length_reverse, List.reverse_reverse] using
    move_left_iterate_mk₂_append «prefix».reverse L R

theorem move_right_then_left_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.left)^[«prefix».length]
        ((Tape.move Dir.right)^[«prefix».length] (Tape.mk₂ L («prefix» ++ R))) =
      Tape.mk₂ L («prefix» ++ R) := by
  rw [move_right_iterate_mk₂_append]
  exact move_left_iterate_reverse_mk₂ «prefix» L R

end TapeWord

end DepthThreeLowerBound

end OAI
