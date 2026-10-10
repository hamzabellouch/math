import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LogBrunnMinkowski

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def OriginSymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x : Space n => ⟪x, u⟫_ℝ) '' K)

def wulff {n : ℕ} (f : Space n → ℝ) : Set (Space n) :=
  {x | ∀ u, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ f u}

def logCombination {n : ℕ} (K L : Set (Space n)) (t : ℝ) :
    Set (Space n) :=
  wulff (fun u => (support K u) ^ (1 - t) * (support L u) ^ t)

theorem main (n : ℕ) (hn : 1 ≤ n) (K L : Set (Space n))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume K) ^ (1 - t) * (volume L) ^ t ≤ volume (logCombination K L t) := by
  sorry

end LogBrunnMinkowski

end

end OAI
