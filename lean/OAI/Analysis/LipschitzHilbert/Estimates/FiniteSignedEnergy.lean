import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! Finite sign randomization in a Hilbert space, expressed without a
probability space. A bound for every signed sum bounds the square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def finiteSignedSum {n : ℕ} (f : Fin n → E) (s : Fin n → Bool) : E :=
  ∑ i, if s i then f i else -f i

theorem finiteSignedSum_energy {n : ℕ} (f : Fin n → E) (x : E) (B : ℝ)
    (h : ∀ s : Fin n → Bool, ‖x+finiteSignedSum f s‖^2≤B) :
    ‖x‖^2+∑ i, ‖f i‖^2≤B := by
  induction n generalizing x B with
  | zero => simpa [finiteSignedSum] using h Fin.elim0
  | succ n ih =>
    let g : Fin n → E := fun i => f i.succ
    have htail (s : Fin n → Bool) :
        ‖x+finiteSignedSum g s‖^2≤B-‖f 0‖^2 := by
      have hp := h (Fin.cons true s)
      have hn := h (Fin.cons false s)
      simp [finiteSignedSum,Fin.sum_univ_succ] at hp hn
      have hp' : ‖(x+finiteSignedSum g s)+f 0‖^2≤B := by
        convert hp using 2
        dsimp [finiteSignedSum,g]
        abel_nf
      have hn' : ‖(x+finiteSignedSum g s)-f 0‖^2≤B := by
        convert hn using 2
        dsimp [finiteSignedSum,g]
        abel_nf
      have hpar := parallelogram_law_with_norm ℂ (x+finiteSignedSum g s) (f 0)
      nlinarith
    have hi := ih g x (B-‖f 0‖^2) htail
    rw [Fin.sum_univ_succ]
    dsimp [g] at hi
    linarith

theorem finiteSignedSum_square_le {n : ℕ} (f : Fin n → E) (B : ℝ)
    (h : ∀ s : Fin n → Bool, ‖finiteSignedSum f s‖^2≤B) :
    (∑ i, ‖f i‖^2)≤B := by
  simpa only [norm_zero,zero_pow (by decide : 2≠0),zero_add] using
    finiteSignedSum_energy f (0:E) B (fun s => by simpa only [zero_add] using h s)

end LipschitzHilbert

end

end OAI
