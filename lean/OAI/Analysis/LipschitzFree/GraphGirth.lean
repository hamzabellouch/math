import OAI.Analysis.LipschitzFree.FiniteQuotients
import OAI.Analysis.LipschitzFree.PortGraphs

namespace OAI

/-!
# Cayley graphs with injective bounded reduced walks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Finite A] [DecidableEq A]

abbrev Cayley (N : ℕ) := Equiv.Perm (WordBall A N)

def invertPort (e : A × Bool) : A × Bool := (e.1, !e.2)

def letter (e : A × Bool) : FreeGroup A :=
  if e.2 then FreeGroup.of e.1 else (FreeGroup.of e.1)⁻¹

omit [Finite A] [DecidableEq A] in
@[simp] theorem letter_invert (e : A × Bool) : letter A (invertPort A e) = (letter A e)⁻¹ := by
  rcases e with ⟨a, b⟩
  cases b <;> simp [letter, invertPort]

def cayleyGraph (N : ℕ) : PortGraph (Cayley A N) (A × Bool) where
  reverse := invertPort A
  reverse_involutive e := by rcases e with ⟨a,b⟩; cases b <;> rfl
  move x e := x * ballRep A N (letter A e)
  move_reverse x e := by rw [letter_invert, map_inv, mul_inv_cancel_right]

theorem cayley_walk (N : ℕ) (x : Cayley A N) (w : List (A × Bool)) :
    (cayleyGraph A N).walk x w = x * ballRep A N (FreeGroup.mk w) := by
  induction w generalizing x with
  | nil =>
    change x = x * ballRep A N 1
    rw [map_one, mul_one]
  | cons e w ih =>
    rcases e with ⟨a,b⟩
    rw [PortGraph.walk_cons, ih, mk_cons_letter, map_mul, ← mul_assoc]
    rfl

theorem cayley_reduced (N : ℕ) (w : List (A × Bool)) :
    (cayleyGraph A N).Reduced w ↔ FreeGroup.IsReduced w := by
  have he : (fun e f : A × Bool => f ≠ invertPort A e) =
      (fun e f : A × Bool => e.1 = f.1 → e.2 = f.2) := by
    funext e f
    apply propext
    rcases e with ⟨a,b⟩
    rcases f with ⟨c,d⟩
    cases b <;> cases d <;> simp [invertPort, eq_comm]
  change w.IsChain (fun e f => f ≠ invertPort A e) ↔ _
  rw [he]
  rfl

theorem cayley_prefix_injective (N : ℕ) (x : Cayley A N) (w : List (A × Bool))
    (hw : (cayleyGraph A N).Reduced w) (hN : w.length ≤ N) :
    Function.Injective (fun i : Fin (w.length+1) => (cayleyGraph A N).walk x (w.take i.val)) := by
  simp only [cayley_walk]
  exact prefixes_injective A N w ((cayley_reduced A N w).mp hw) hN x

def allColoringsGraph (C : Type*) (N : ℕ) :
    PortGraph ((Cayley A N → C) × Cayley A N) (A × Bool) where
  reverse := invertPort A
  reverse_involutive := (cayleyGraph A N).reverse_involutive
  move x e := (x.1, (cayleyGraph A N).move x.2 e)
  move_reverse x e := by
    change (x.1, (cayleyGraph A N).move ((cayleyGraph A N).move x.2 e)
      ((cayleyGraph A N).reverse e)) = x
    rw [(cayleyGraph A N).move_reverse]

def allColoringsColor (C : Type*) (N : ℕ) (x : (Cayley A N → C) × Cayley A N) : C := x.1 x.2

theorem allColorings_walk (C : Type*) (N : ℕ)
    (x : (Cayley A N → C) × Cayley A N) (w : List (A × Bool)) :
    (allColoringsGraph A C N).walk x w = (x.1, (cayleyGraph A N).walk x.2 w) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih _

theorem allColorings_reduced (C : Type*) (N : ℕ) (w : List (A × Bool)) :
    (allColoringsGraph A C N).Reduced w ↔ (cayleyGraph A N).Reduced w := Iff.rfl

end DiscreteFree.GraphProducer
end

end

end OAI
