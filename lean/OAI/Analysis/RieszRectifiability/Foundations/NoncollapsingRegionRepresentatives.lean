import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.RegionRepresentativeGeometry
import OAI.Analysis.RieszRectifiability.Projections.NoncollapsingPlaneProjection

namespace OAI

/-!
# Projection separation of region representatives

A good cell containing two region representatives supplies a common fitted
plane. Its noncollapsing projection estimate and the tube error bound give
quantitative separation of the representatives after projection.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem projection_separates_noncollapsing_region_representatives {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ) (hσ : 0 ≤ σ) (hκ : 0 < κ)
    (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hfit : ∀ i : SupportCellDescendant μ R hR k z, Good i →
      ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
        (∀ w ∈ ball i.center (1024 * i.radius), w ∈ μ.support →
          infDist w (S : Set (Ambient d)) ≤ σ * i.radius) ∧
        ∀ v ∈ S.direction, κ * ‖v‖ ≤ ‖P.starProjection v‖) :
    ∀ x ∈ cellRegionRepresentatives μ R hR k z Good,
    ∀ y ∈ cellRegionRepresentatives μ R hR k z Good,
      dist x y ≤ (2 / κ) * dist (P.starProjection x) (P.starProjection y) := by
  intro x hx y hy
  by_cases hxy : x = y
  · simp only [hxy, dist_self, mul_zero, le_refl]
  obtain ⟨q, hgood, _, hupper, _, hxball, hyball⟩ :=
    exists_good_pair_cell_for_representatives μ R hR k z Good hroot x y hx hy hxy
  obtain ⟨S, hS, htube, hlower⟩ := hfit q hgood
  let : Nonempty S := hS.1.to_subtype
  have hxμ := supportLatticeCell_subset_support μ R hR k z
    (cellRegionRepresentatives_subset_top μ R hR k z Good hx).1
  have hyμ := supportLatticeCell_subset_support μ R hR k z
    (cellRegionRepresentatives_subset_top μ R hR k z Good hy).1
  have hb : σ * q.radius ≤ (512 * σ) * dist x y := by
    have h := mul_le_mul_of_nonneg_left hupper hσ
    nlinarith
  have hxS := (htube x hxball hxμ).trans hb
  have hyS := (htube y hyball hyμ).trans hb
  exact projection_separates_of_lower_bound P.starProjection S x y (512 * σ) κ hκ
    (by nlinarith) (fun v => P.norm_starProjection_apply_le v) hxS hyS hlower

theorem exists_cover_of_noncollapsing_region_representatives {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (σ : ℝ) (κ : ℝ≥0) (hσ : 0 ≤ σ) (hκ : 0 < κ)
    (hsmall : 2048 * σ * ((κ : ℝ) + 1) ≤ κ)
    (hfit : ∀ i : SupportCellDescendant μ R hR k z, Good i →
      ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
        (∀ w ∈ ball i.center (1024 * i.radius), w ∈ μ.support →
          infDist w (S : Set (Ambient d)) ≤ σ * i.radius) ∧
        ∀ v ∈ S.direction, (κ : ℝ) * ‖v‖ ≤ ‖P.starProjection v‖) :
    ∃ g : (ball (0 : Ambient n) (3 * latticeRadius R k)) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * (2 / κ)) g ∧
        cellRegionRepresentatives μ R hR k z Good ⊆ range g := by
  have hball : cellRegionRepresentatives μ R hR k z Good ⊆
      ball (z : Ambient d) (3 * latticeRadius R k) := by
    intro x hx
    have hb := (supportLatticeCell_bounds μ R hR k z).2
      (cellRegionRepresentatives_subset_top μ R hR k z Good hx).1
    change dist x (z : Ambient d) ≤ 2 * latticeRadius R k at hb
    rw [mem_ball]
    have hr := latticeRadius_pos R hR k
    linarith
  apply exists_ball_lipschitz_cover_of_projection _ _ _ hball P hdim (2 / κ)
  simpa only [NNReal.coe_div, NNReal.coe_ofNat] using!
    projection_separates_noncollapsing_region_representatives μ R hR k z Good hroot P
      σ κ hσ hκ hsmall hfit

end

end RieszRectifiability

end OAI
