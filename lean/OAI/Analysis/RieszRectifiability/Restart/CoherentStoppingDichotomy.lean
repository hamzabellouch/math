import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CoherentRegionParameterization

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem projection_squared_loss_of_normal_angle {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (v : Ambient d)
    (hangle : (1 / 4 : ℝ) * ‖v‖ < ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖) :
    v ≠ 0 ∧ ‖P.starProjection v‖ ^ 2 < (15 / 16 : ℝ) * ‖v‖ ^ 2 := by
  have hne : v ≠ 0 := by
    intro hz
    simp only [hz, map_zero, norm_zero, mul_zero, lt_self_iff_false] at hangle
  have hs := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ (1 / 4) * ‖v‖) hangle
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection v P
  refine ⟨hne, ?_⟩
  nlinarith

theorem incoherent_beta_good_cell_has_angle_witness {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (P : Submodule ℝ (Ambient d))
    (i : SupportCellDescendant μ R hR k z)
    (hnot : ¬cellHasCoherentPlane n μ R hR k z P i)
    (hbeta : bilateralBeta n μ i.center (1024 * i.radius) < 1 / 1024) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      bilateralPlaneError μ i.center (1024 * i.radius) S < 1 / 1024 ∧
      ∃ v ∈ S.direction, v ≠ 0 ∧
        (1 / 4 : ℝ) * ‖v‖ < ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ∧
        ‖P.starProjection v‖ ^ 2 < (15 / 16 : ℝ) * ‖v‖ ^ 2 := by
  classical
  obtain ⟨S, hS, herr⟩ := exists_bilateral_plane_error_lt hnd μ i.center
    (1024 * i.radius) (1 / 1024) hbeta
  have hbad : ¬∀ v ∈ S.direction,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4 : ℝ) * ‖v‖ := by
    intro hangle
    exact hnot ⟨S, hS, herr, hangle⟩
  push Not at hbad
  obtain ⟨v, hv, hangle⟩ := hbad
  have hloss := projection_squared_loss_of_normal_angle P v hangle
  exact ⟨S, hS, herr, v, hv, hloss.1, hangle, hloss.2⟩

theorem coherent_region_stop_dichotomy {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (P : Submodule ℝ (Ambient d))
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z (cellHasCoherentPlane n μ R hR k z P)) :
    (1 / 1024 : ℝ) ≤ bilateralBeta n μ i.center (1024 * i.radius) ∨
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      bilateralPlaneError μ i.center (1024 * i.radius) S < 1 / 1024 ∧
      ∃ v ∈ S.direction, v ≠ 0 ∧
        (1 / 4 : ℝ) * ‖v‖ < ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ∧
        ‖P.starProjection v‖ ^ 2 < (15 / 16 : ℝ) * ‖v‖ ^ 2 := by
  by_cases hb : (1 / 1024 : ℝ) ≤ bilateralBeta n μ i.center (1024 * i.radius)
  · exact Or.inl hb
  · exact Or.inr (incoherent_beta_good_cell_has_angle_witness hnd μ R hR k z P i hi.1
      (lt_of_not_ge hb))

end

end RieszRectifiability

end OAI
