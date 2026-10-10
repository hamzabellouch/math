import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactPairs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! # Lower quasi-isometry bounds from Lipschitz coarse inverses -/

namespace PolycyclicRecognition

open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A Lipschitz inverse with bounded composition error supplies the lower
inequality, with the same enlarged constant used by the compact pair space. -/
theorem coarse_lower_of_lipschitz_inverse
    {Λ : ℝ≥0} (hΛ : 2 ≤ (Λ : ℝ)) (f : X → Y) (g : Y → X)
    (hg : LipschitzWith Λ g) (hinv : ∀ x, dist (g (f x)) x ≤ Λ) (x y : X) :
    (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (f x) (f y) := by
  have hpos : 0 < (Λ : ℝ) := lt_of_lt_of_le (by norm_num) hΛ
  have hd : dist x y ≤ (Λ : ℝ) + Λ * dist (f x) (f y) + Λ := by
    calc
      dist x y ≤ dist x (g (f x)) + dist (g (f x)) (g (f y)) + dist (g (f y)) y :=
        dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) + Λ * dist (f x) (f y) + Λ :=
        add_le_add (add_le_add (by simpa only [dist_comm] using hinv x)
          (hg.dist_le_mul _ _)) (hinv y)
  have hdiv : (Λ : ℝ)⁻¹ * dist x y ≤ dist (f x) (f y) + 2 := by
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    nlinarith only [hd]
  linarith only [hdiv, hΛ]

variable {G : Type*} [Group G] [MetricSpace G]

omit [Group G] in
/-- No separate lower-bound hypothesis is needed once the two Lipschitz
representatives have controlled inverse errors. -/
theorem lipschitzPairBounds_of_inverse_bounds
    {Λ : ℝ≥0} (hΛ : 2 ≤ (Λ : ℝ)) (p : C(G, G) × C(G, G))
    (hf : LipschitzWith Λ p.1) (hg : LipschitzWith Λ p.2)
    (hgf : ∀ x, dist (p.2 (p.1 x)) x ≤ Λ)
    (hfg : ∀ x, dist (p.1 (p.2 x)) x ≤ Λ) :
    LipschitzPairBounds G Λ p :=
  ⟨hf, hg, coarse_lower_of_lipschitz_inverse hΛ p.1 p.2 hg hgf,
    coarse_lower_of_lipschitz_inverse hΛ p.2 p.1 hf hfg, hgf, hfg⟩

end PolycyclicRecognition

end OAI
