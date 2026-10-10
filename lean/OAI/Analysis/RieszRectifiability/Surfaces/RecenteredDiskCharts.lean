import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.CoveredProjectionCharts

namespace OAI

/-!
# Recentering disk charts

A chart whose projection is the identity restricts to any closed disk contained in
its parameter disk. The recentered chart preserves the normal Lipschitz bound and
parametrizes exactly the part of the original range over the smaller disk.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_recentered_disk_chart {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (a : P) (ρ : ℝ)
    (g : closedBall a ρ → Ambient d) (L : ℝ≥0)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (b : P) (r : ℝ) (hcontain : dist b a + r ≤ ρ) :
    ∃ h : closedBall b r → Ambient d,
      LipschitzWith (1 + L) h ∧
      LipschitzWith L (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ Set.range g ∧ P.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = Set.range g ∩ P.orthogonalProjectionOnto ⁻¹' closedBall b r := by
  have hcover : closedBall b r ⊆ P.orthogonalProjectionOnto '' Set.range g := by
    intro v hv
    have hnear : v ∈ closedBall a ρ := by
      have ht := dist_triangle v b a
      have hv' : dist v b ≤ r := hv
      change dist v a ≤ ρ
      linarith
    let u : closedBall a ρ := ⟨v, hnear⟩
    exact ⟨g u, ⟨u, rfl⟩, hcoordinates u⟩
  have hstar (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hcone : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (L : ℝ) * dist (P.starProjection x) (P.starProjection y) := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    have h := hnormal.dist_le_mul u v
    rw [dist_eq_norm, ← map_sub] at h
    rw [hstar u, hstar v]
    exact h
  exact exists_chart_on_covered_projection P (Set.range g) L (closedBall b r) hcover hcone

end

end RieszRectifiability

end OAI
