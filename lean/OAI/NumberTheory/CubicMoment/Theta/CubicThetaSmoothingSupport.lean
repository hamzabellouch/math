import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEuclideanSmoothing
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Coordinate smoothing can keep all supports inside one compact
subset of the chosen open chart. -/
noncomputable section
open Set Metric
open scoped Pointwise ContDiff
namespace CubicFirstMoment

lemma cubicThetaSmoothing_compact_chart {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {U : Set (ℂ × ℝ)} (hU : IsOpen U) (hs : tsupport g⊆U) :
    ∃ K : Set (ℂ × ℝ), IsCompact K ∧ tsupport g⊆K ∧ K⊆U ∧
      ∀ ε : ℝ, 0<ε → ∃ h : ℂ × ℝ → ℂ,
        ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h⊆K ∧
        (∀ x, ‖h x-g x‖≤ε) ∧ (∀ x, ‖fderiv ℝ h x-fderiv ℝ g x‖≤ε) := by
  obtain ⟨ρ,hρ,hsub⟩ := hc.exists_cthickening_subset_open hU hs
  refine ⟨cthickening ρ (tsupport g),hc.cthickening,
    self_subset_cthickening _,hsub,?_⟩
  intro ε hε
  obtain ⟨φ,hφ,hv,hd⟩ := cubicThetaCoordinateSmooth_exists hg hc hε hρ
  refine ⟨cubicThetaCoordinateSmooth φ g,
    cubicThetaCoordinateSmooth_contDiff φ hg.continuous,
    cubicThetaCoordinateSmooth_compact φ hc,?_,hv,hd⟩
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := cubicThetaCoordinateSmooth_support φ hc hx
  apply mem_cthickening_of_dist_le (a+b) b ρ (tsupport g) hb
  have ha' : ‖a‖≤φ.rOut := by simpa only [mem_closedBall,dist_zero_right] using ha
  simpa only [dist_eq_norm,add_sub_cancel_right] using ha'.trans hφ.le

end CubicFirstMoment

end

end OAI
