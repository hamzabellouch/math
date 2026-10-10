import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBetaWitnesses
import OAI.Analysis.RieszRectifiability.Nets.CellRegionMass
import OAI.Analysis.RieszRectifiability.Surfaces.CoherentCellCharts

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def cellHasCoherentPlane {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (i : SupportCellDescendant μ R hR k z) : Prop :=
  ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
    bilateralPlaneError μ i.center (1024 * i.radius) S < 1 / 1024 ∧
    ∀ v ∈ S.direction,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4) * ‖v‖

theorem cellHasCoherentPlane_beta_lt {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (i : SupportCellDescendant μ R hR k z)
    (hi : cellHasCoherentPlane n μ R hR k z P i) :
    bilateralBeta n μ i.center (1024 * i.radius) < 1 / 1024 := by
  obtain ⟨S, hS, herr, _⟩ := hi
  exact (bilateralBeta_le_planeError n μ i.center (1024 * i.radius)
    (mul_nonneg (by norm_num) i.radius_pos.le) S hS).trans_lt herr

theorem exists_ball_lipschitz_cover_of_coherent_region {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n) :
    ∃ g : (ball (0 : Ambient n) (3 * latticeRadius R k)) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧
        cellRegionLimit μ R hR k z (cellHasCoherentPlane n μ R hR k z P) ⊆ range g := by
  let Good := cellHasCoherentPlane n μ R hR k z P
  let E := cellRegionLimit μ R hR k z Good
  have hE : E ⊆ cleanSupportCell μ R hR k z := fun _ hx => hx.1
  have hball : E ⊆ ball (z : Ambient d) (3 * latticeRadius R k) := by
    intro x hx
    have hb := (supportLatticeCell_bounds μ R hR k z).2 (hE hx).1
    change dist x (z : Ambient d) ≤ 2 * latticeRadius R k at hb
    rw [mem_ball]
    have hr := latticeRadius_pos R hR k
    linarith
  apply exists_ball_lipschitz_cover_of_coherent_cell_fits μ R hR k z E hE
    (z : Ambient d) (3 * latticeRadius R k) hball P hdim
  intro i hi
  obtain ⟨x, hxE, hxi⟩ := hi
  obtain ⟨S, hS, herr, hangle⟩ := hxE.2 i hxi
  obtain ⟨hforward, _⟩ := bilateralPlaneError_lt_pointwise μ
    ⟨i.center, i.center_mem_support⟩ i.center (1024 * i.radius) (1 / 1024)
    (mul_pos (by norm_num) i.radius_pos) S hS herr
  refine ⟨S, hS, ?_, hangle⟩
  intro w hw
  have hwS := supportLatticeCell_subset_support μ R hR k z (hE hw.1).1
  have ht := hforward w hw.2 hwS
  nlinarith

theorem coherent_region_chart_with_stopping_mass {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n) :
    ∃ g : (ball (0 : Ambient n) (3 * latticeRadius R k)) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧
        μ (cleanSupportCell μ R hR k z) ≤ μ (cleanSupportCell μ R hR k z ∩ range g) +
          ∑' i : cellRegionStops μ R hR k z (cellHasCoherentPlane n μ R hR k z P), μ i.val.cell := by
  obtain ⟨g, hLip, hcover⟩ := exists_ball_lipschitz_cover_of_coherent_region μ R hR k z P hdim
  refine ⟨g, hLip, ?_⟩
  rw [cellRegion_mass_identity μ R hR k z (cellHasCoherentPlane n μ R hR k z P)]
  apply add_le_add _ le_rfl
  apply measure_mono
  intro x hx
  exact ⟨hx.1, hcover hx⟩

end

end RieszRectifiability

end OAI
