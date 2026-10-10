import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Branching.SmoothTestFamily
import Mathlib.Analysis.Convex.Measure

namespace OAI

/-! # Compact smooth spacetime cutoffs covering almost all of the physical cell -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.TorusKineticChart

def interiorRegion : Set Published.SpaceTime := Ioi (0 : ℝ) ×ˢ interior TorusChart.cube

theorem interiorRegion_open : IsOpen interiorRegion := isOpen_Ioi.prod isOpen_interior

theorem cube_convex : Convex ℝ TorusChart.cube := by
  intro x hx y hy a b ha hb hab i
  have hi := (convex_Ioc (-(1/2:ℝ)) (1/2)) (hx i) (hy i) ha hb hab
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,TorusChart.interval] using hi

theorem zero_mem_interior_cube : (0 : Velocity) ∈ interior TorusChart.cube := by
  apply mem_interior_iff_mem_nhds.mpr
  have hb : Metric.ball (0 : Velocity) (1/4) ⊆ TorusChart.cube := by
    intro x hx i
    have hxnorm : ‖x‖ < 1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have habs : |x i| < 1/4 := hi.trans_lt hxnorm
    have hh := abs_lt.mp habs
    change -(1/2:ℝ) < x i ∧ x i ≤ 1/2
    constructor <;> linarith
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Velocity) (by norm_num)) hb

theorem interiorRegion_nonempty : interiorRegion.Nonempty :=
  ⟨(1,0),by norm_num [interiorRegion]; exact zero_mem_interior_cube⟩

theorem interior_cube_ae : ∀ᵐ x ∂((volume : Measure Velocity).restrict TorusChart.cube),
    x ∈ interior TorusChart.cube := by
  have hfront := cube_convex.addHaar_frontier (volume : Measure Velocity)
  have hnull : ∀ᵐ x ∂(volume : Measure Velocity), x ∉ frontier TorusChart.cube := by
    apply ae_iff.mpr
    simpa only [Classical.not_not,Set.ofPred_mem_eq] using hfront
  apply (ae_restrict_iff' TorusChart.measurableSet_cube).mpr
  filter_upwards [hnull] with x hx hxc
  by_contra hi
  exact hx ⟨subset_closure hxc,hi⟩

theorem interiorRegion_ae (T : ℝ) : ∀ᵐ z ∂baseVolume T, z ∈ interiorRegion := by
  have ht : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Icc 0 T)), 0 < t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with t ht hn
    exact lt_of_le_of_ne ht.1 (Ne.symm hn)
  exact Measure.ae_prod_iff_ae_ae (interiorRegion_open.measurableSet) |>.mpr
    (ht.mono (fun _ ht => interior_cube_ae.mono (fun _ hx => ⟨ht,hx⟩)))

end BoltzmannNonuniqueness.TorusKineticChart

end

end OAI
