import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.RegionRepresentativeCharts

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def cellHasFineCoherentPlane {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (i : SupportCellDescendant μ R hR k z) : Prop :=
  ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
    bilateralPlaneError μ i.center (1024 * i.radius) S < 1 / 16777216 ∧
    ∀ v ∈ S.direction,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4 : ℝ) * ‖v‖

theorem SupportCellDescendant.zero_depth_geometry {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    i.center = (z : Ambient d) ∧ i.radius = latticeRadius R k := by
  have hc := congrArg Subtype.val i.ancestor
  constructor
  · simpa only [supportLatticeAncestor, supportLatticeCenter, hi, netAncestor_zero] using! hc
  · simp only [SupportCellDescendant.radius, hi, Nat.add_zero]

theorem fine_coherent_cell_plane_fits {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (i : SupportCellDescendant μ R hR k z)
    (hi : cellHasFineCoherentPlane n μ R hR k z P i) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      (∀ w ∈ ball i.center (1024 * i.radius), w ∈ μ.support →
        infDist w (S : Set (Ambient d)) ≤ i.radius / 16384) ∧
      ∀ v ∈ S.direction,
        ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4 : ℝ) * ‖v‖ := by
  obtain ⟨S, hS, herr, hangle⟩ := hi
  obtain ⟨hforward, _⟩ := bilateralPlaneError_lt_pointwise μ
    ⟨i.center, i.center_mem_support⟩ i.center (1024 * i.radius) (1 / 16777216)
    (mul_pos (by norm_num) i.radius_pos) S hS herr
  refine ⟨S, hS, ?_, hangle⟩
  intro w hw hμ
  have h := hforward w hw hμ
  linarith

theorem fine_coherent_cell_implies_coherent {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (i : SupportCellDescendant μ R hR k z)
    (hi : cellHasFineCoherentPlane n μ R hR k z P i) :
    cellHasCoherentPlane n μ R hR k z P i := by
  obtain ⟨S, hS, herr, hangle⟩ := hi
  exact ⟨S, hS, herr.trans (by norm_num), hangle⟩

theorem fine_coherent_root_good {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (herr : bilateralPlaneError μ (z : Ambient d) (1024 * latticeRadius R k) S < 1 / 16777216)
    (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    cellHasFineCoherentPlane n μ R hR k z S.direction i := by
  obtain ⟨hc, hr⟩ := i.zero_depth_geometry hi
  refine ⟨S, hS, ?_, ?_⟩
  · simpa only [hc, hr] using! herr
  · intro v hv
    rw [S.direction.starProjection_orthogonal_val, S.direction.starProjection_eq_self_iff.mpr hv,
      sub_self, norm_zero]
    exact mul_nonneg (by norm_num) (norm_nonneg v)

theorem exists_representative_chart_of_fine_root_fit {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (herr : bilateralPlaneError μ (z : Ambient d) (1024 * latticeRadius R k) S < 1 / 16777216) :
    ∃ g : (ball (0 : Ambient n) (3 * latticeRadius R k)) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧
        cellRegionRepresentatives μ R hR k z (cellHasFineCoherentPlane n μ R hR k z S.direction) ⊆ range g := by
  exact exists_ball_lipschitz_cover_of_region_representatives μ R hR k z
    (cellHasFineCoherentPlane n μ R hR k z S.direction)
    (fine_coherent_root_good μ R hR k z S hS herr) S.direction hS.2
    (fine_coherent_cell_plane_fits μ R hR k z S.direction)

theorem exists_fine_region_chart_of_beta_lt {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (hbeta : bilateralBeta n μ (z : Ambient d) (1024 * latticeRadius R k) < 1 / 16777216) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      ∃ g : (ball (0 : Ambient n) (3 * latticeRadius R k)) → Ambient d,
        LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧
          cellRegionRepresentatives μ R hR k z (cellHasFineCoherentPlane n μ R hR k z P) ⊆ range g := by
  obtain ⟨S, hS, herr⟩ := exists_bilateral_plane_error_lt hnd μ (z : Ambient d)
    (1024 * latticeRadius R k) (1 / 16777216) hbeta
  obtain ⟨g, hLip, hcover⟩ := exists_representative_chart_of_fine_root_fit μ R hR k z S hS herr
  exact ⟨S.direction, hS.2, g, hLip, hcover⟩

end

end RieszRectifiability

end OAI
