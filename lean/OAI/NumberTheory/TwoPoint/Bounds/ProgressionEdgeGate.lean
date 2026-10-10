import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
import Mathlib.Data.Int.ModEq

namespace OAI

/-! The progression restriction is symmetric in the two endpoints and
is fixed while the block origin moves through one residue class. -/

namespace TwoPointCorrelations

def progressionEdgeGate (h l b d : ℕ) (n m : ℤ) : Prop :=
  ∃ q : ℕ,
    (m = n + (h * q * d : ℕ) ∧ Int.ModEq (l : ℤ) n (b * q * d : ℕ)) ∨
    (n = m + (h * q * d : ℕ) ∧ Int.ModEq (l : ℤ) m (b * q * d : ℕ))

lemma progressionEdgeGate_symmetric (h l b d : ℕ) (n m : ℤ) :
    progressionEdgeGate h l b d n m ↔ progressionEdgeGate h l b d m n := by
  simp only [progressionEdgeGate, or_comm]

lemma progressionEdgeGate_add_mul (h l b d : ℕ) (n m k : ℤ) :
    progressionEdgeGate h l b d (n + l * k) (m + l * k) ↔
      progressionEdgeGate h l b d n m := by
  unfold progressionEdgeGate
  apply exists_congr
  intro q
  have he₁ : m + l * k = n + l * k + (h * q * d : ℕ) ↔
      m = n + (h * q * d : ℕ) := by omega
  have he₂ : n + l * k = m + l * k + (h * q * d : ℕ) ↔
      n = m + (h * q * d : ℕ) := by omega
  simp only [he₁, he₂, Int.add_modulus_mul_modEq_iff]

lemma progressionEdgeGate_freeze (h l b d : ℕ) (n m a : ℤ) (k : ℕ) :
    progressionEdgeGate h l b d (n + (a + l * k)) (m + (a + l * k)) ↔
      progressionEdgeGate h l b d (n + a) (m + a) := by
  simpa only [← add_assoc] using progressionEdgeGate_add_mul h l b d (n + a) (m + a) k

end TwoPointCorrelations

end OAI
