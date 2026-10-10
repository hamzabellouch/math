import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineCompression
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionEdgeGate

namespace OAI

/-! Freeze the ambient progression condition within each residue class
before applying the affine-origin compression estimate. -/

namespace TwoPointCorrelations

open scoped Classical

lemma progressionEdgeGate_function (h l b : ℕ) (a : ℤ) (k : ℕ) :
    (fun d n m => progressionEdgeGate h l b d (n + (a + l * k)) (m + (a + l * k))) =
      (fun d n m => progressionEdgeGate h l b d (n + a) (m + a)) := by
  funext d n m
  exact propext (progressionEdgeGate_freeze h l b d n m a k)

lemma primeBlockCompression_progression_freeze {J : ℕ} (P : Fin J → Finset ℕ)
    (M : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h l b : ℕ)
    (keep : ℤ → Prop) (a : ℤ) (k : ℕ) :
    primeBlockCompression P M Q u eligible g L K W extra h
      (fun d n m => progressionEdgeGate h l b d (n + (a + l * k)) (m + (a + l * k)))
      keep (a + l * k) =
    primeBlockCompression P M Q u eligible g L K W extra h
      (fun d n m => progressionEdgeGate h l b d (n + a) (m + a)) keep (a + l * k) := by
  rw [progressionEdgeGate_function]

end TwoPointCorrelations

end OAI
