import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RadixEncoding
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.GappedInstructions

namespace OAI

/-!
# Symbolic tape updates give the closed-rectangle affine maps

The first stream lists cells to the left of the head, nearest first; the
second starts at the current cell. The three formulas include writing the
new symbol before moving the head.
-/

noncomputable section

namespace ForcedComputation.Radix

variable {A : Type*}

abbrev Tape (A : Type*) := (ℕ → A) × (ℕ → A)

def coordinates (B : ℝ) (digit : A → ℝ) (tape : Tape A) : ℝ × ℝ :=
  (encode B digit tape.1, encode B digit tape.2)

def writeRight (b : A) (tape : Tape A) : Tape A :=
  (prepend b tape.1, fun n => tape.2 (n + 1))

def writeStay (b : A) (tape : Tape A) : Tape A :=
  (tape.1, prepend b (fun n => tape.2 (n + 1)))

def writeLeft (b : A) (tape : Tape A) : Tape A :=
  (fun n => tape.1 (n + 1), prepend (tape.1 0) (prepend b (fun n => tape.2 (n + 1))))

theorem encode_pop {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (u : ℕ → A) :
    pop B (digit (u 0)) (encode B digit u) = encode B digit (fun n => u (n + 1)) := by
  rw [encode_shift hB hd]
  exact pop_push (by linarith) _ _

theorem coordinates_right {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (b : A) (tape : Tape A) :
    coordinates B digit (writeRight b tape) =
      rightMove B (digit (tape.2 0)) (digit b) (coordinates B digit tape) := by
  apply Prod.ext
  · exact encode_prepend hB hd b tape.1
  · exact (encode_pop hB hd tape.2).symm

theorem coordinates_stay {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (b : A) (tape : Tape A) :
    coordinates B digit (writeStay b tape) =
      stayMove B (digit (tape.2 0)) (digit b) (coordinates B digit tape) := by
  apply Prod.ext
  · rfl
  · change encode B digit (prepend b (fun n => tape.2 (n + 1))) = _
    rw [encode_prepend hB hd]
    change push B (digit b) (encode B digit (fun n => tape.2 (n + 1))) =
      push B (digit b) (pop B (digit (tape.2 0)) (encode B digit tape.2))
    rw [encode_pop hB hd]

theorem coordinates_left {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (b : A) (tape : Tape A) :
    coordinates B digit (writeLeft b tape) =
      leftMove B (digit (tape.1 0)) (digit (tape.2 0)) (digit b) (coordinates B digit tape) := by
  apply Prod.ext
  · exact (encode_pop hB hd tape.1).symm
  · change encode B digit (prepend (tape.1 0) (prepend b (fun n => tape.2 (n + 1)))) = _
    rw [encode_prepend hB hd, encode_prepend hB hd]
    change push B (digit (tape.1 0)) (push B (digit b)
      (encode B digit (fun n => tape.2 (n + 1)))) =
      push B (digit (tape.1 0)) (push B (digit b)
        (pop B (digit (tape.2 0)) (encode B digit tape.2)))
    rw [encode_pop hB hd]

theorem coordinates_mem_rectangle {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (tape : Tape A) :
    coordinates B digit tape ∈ rectangle B (digit (tape.1 0)) (digit (tape.2 0)) :=
  ⟨encode_in_first_cylinder hB hd tape.1, encode_in_first_cylinder hB hd tape.2⟩

end ForcedComputation.Radix

end

end OAI
