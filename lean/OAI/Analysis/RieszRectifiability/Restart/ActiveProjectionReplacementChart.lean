import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionDiskCoverage
import OAI.Analysis.RieszRectifiability.Projections.CoveredProjectionCharts

namespace OAI

/-!
# Replacement charts on active projection images

The active projection of a tangentially parametrized disk satisfies a quantitative cone bound
and covers a smaller disk in the reference plane. These properties produce a replacement chart
with exact tangential coordinates, Lipschitz constant at most two, and controlled normal slope.
Its range is precisely the portion of the projected image lying above the smaller disk.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_level_replacement_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (a : (S q).direction) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : closedBall a ρ → Ambient d) (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    let P := (S q).direction
    let δ := (262144 * ε) * latticeRadius R (k + t)
    let D := closedBall a (ρ - δ)
    let A := (activeLevelProjectionMap μ R hR k z Good t S hS) '' Set.range g
    ∃ h : D → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε))
        (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ A ∧ P.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = A ∩ P.orthogonalProjectionOnto ⁻¹' D := by
  let P := (S q).direction
  let η := activeProjectionError d ε
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  let δ := (262144 * ε) * latticeRadius R (k + t)
  let D := closedBall a (ρ - δ)
  let A := σ '' Set.range g
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have hstar (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hinput : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y) := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    rw [hstar u, hstar v]
    simpa only [NNReal.coe_ofNat] using! hg.dist_le_mul u v
  have herr : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(σ x - σ y) - P.starProjection (x - y)‖ ≤ η * dist x y := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    exact activeLevelProjectionMap_reference_increment μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (g u) (g v) (hlocal u) (hlocal v)
  have hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (Real.toNNReal (4 * η) : ℝ) * dist (P.starProjection x) (P.starProjection y) := by
    intro x hx y hy
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
    exact projection_perturbation_image_cone P (Set.range g) σ η hη hsmall hinput herr x hx y hy
  have hcover : D ⊆ P.orthogonalProjectionOnto '' A := by
    have hc := activeLevelProjectionMap_covers_shrunk_disk μ R hR k z Good t S hS
      ε hε hsmall hfit q hq a ρ hρ g hg hcoordinates hlocal
    intro b hb
    obtain ⟨u, hu⟩ := hc hb
    exact ⟨σ (g u), ⟨g u, ⟨u, rfl⟩, rfl⟩, hu⟩
  obtain ⟨h, hLip, hnLip, hcoords, hrange⟩ :=
    exists_chart_on_covered_projection P A (Real.toNNReal (4 * η)) D hcover hcone
  have hL : 1 + Real.toNNReal (4 * η) ≤ (2 : ℝ≥0) := by
    have hh : ((1 + Real.toNNReal (4 * η) : ℝ≥0) : ℝ) ≤ 2 := by
      rw [NNReal.coe_add, NNReal.coe_one,
        Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
      change η ≤ 1 / 4 at hsmall
      linarith
    exact_mod_cast hh
  exact ⟨h, hLip.weaken hL, hnLip, hcoords, hrange⟩

end

end RieszRectifiability

end OAI
