import Mathlib

namespace OAI

open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar

abbrev Position (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Phase (n : ℕ) := Position n × Position n

def IsSymmetricConvexBody {n : ℕ} (K : Set (Position n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    ∀ x, x ∈ K ↔ -x ∈ K

def polar {n : ℕ} (K : Set (Position n)) : Set (Position n) :=
  {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}

def polarProduct {n : ℕ} (K : Set (Position n)) : Set (Phase n) :=
  interior K ×ˢ interior (polar K)

def capacityBall (n : ℕ) (c : ℝ) : Set (Phase n) :=
  {z | Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < c}

noncomputable def omega0 {n : ℕ} (v w : Phase n) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2 - inner (𝕜 := ℝ) w.1 v.2

def HasSymplecticEmbedding {n : ℕ} (U V : Set (Phase n)) : Prop :=
  ∃ e : Phase n → Phase n,
    ContDiffOn ℝ ∞ e U ∧
    Topology.IsEmbedding (fun z : U => e z) ∧
    MapsTo e U V ∧
    ∀ z ∈ U, ∀ v w : Phase n,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w

noncomputable def gromovWidth {n : ℕ} (U : Set (Phase n)) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {c : ℝ | 0 < c ∧ HasSymplecticEmbedding (capacityBall n c) U})

theorem symmetric_polar_main {n : ℕ} (hn : 2 ≤ n)
    (K : Set (Position n)) (hK : IsSymmetricConvexBody K) :
    gromovWidth (polarProduct K) = 4 ∧
      ∀ c : ℝ, 0 < c → c < 4 →
        HasSymplecticEmbedding (capacityBall n c) (polarProduct K) := by
  sorry

end SymmetricPolar

end OAI
