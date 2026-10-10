import OAI.MeasureTheory.Falconer.Estimates.LocalInverse
import OAI.MeasureTheory.Falconer.Angular.SphereStationaryAssembly

namespace OAI

/-! # The inverse amplitudes have no incoming-pole contribution

Their fixed patch support places the opposite prepared direction outside
their support. Locality of the actual stationary coefficients then removes
all incoming coefficients, without a differential-operator assumption.
-/

namespace Falconer
open Set
open scoped Topology

theorem prepared_direction_opposite_far (m : ℕ) (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    1/4 < ‖-(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ := by
  let p : Space (m+3) := gnomonicChart (0 : Space (m+2))
  have htwo : ‖(p-(e : Space (m+3)))+((e : Space (m+3))+p)‖ = 2 := by
    have heq : (p-(e : Space (m+3)))+((e : Space (m+3))+p) = (2 : ℝ) • p := by module
    rw [heq,norm_smul]
    change ‖(2 : ℝ)‖*‖(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ = 2
    rw [sphere_norm]
    norm_num
  have ht := norm_add_le (p-(e : Space (m+3))) ((e : Space (m+3))+p)
  rw [htwo,norm_sub_rev p (e : Space (m+3))] at ht
  have hn : ‖-(e : Space (m+3))-p‖ = ‖(e : Space (m+3))+p‖ := by
    rw [show -(e : Space (m+3))-p = -((e : Space (m+3))+p) by abel,norm_neg]
  change 1/4 < ‖-(e : Space (m+3))-p‖
  rw [hn]
  change ‖(e : Space (m+3))-p‖ ≤ 1/8 at he
  linarith

theorem localInverseAmplitude_antipodal_coefficient_zero (m j h : ℕ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    actualStationaryCoefficient m h (antipodalConjugate (localInverseAmplitude m B j)) e = 0 := by
  have hfar := prepared_direction_opposite_far m e he
  have hout : -(e : Space (m+3)) ∉ tsupport (localInverseAmplitude m B j) := by
    intro hm
    have hc := localInverseAmplitude_tsupport m j B hm
    rw [stationaryPatchMask_support,Metric.mem_closedBall,dist_eq_norm] at hc
    exact (not_le.mpr hfar) hc
  have hz := notMem_tsupport_iff_eventuallyEq.mp hout
  have hneg : Filter.Tendsto (fun x : Space (m+3) => -x)
      (𝓝 (e : Space (m+3))) (𝓝 (-(e : Space (m+3)))) :=
    continuous_neg.continuousAt
  have heq : antipodalConjugate (localInverseAmplitude m B j) =ᶠ[𝓝 (e : Space (m+3))]
      (fun _ => 0) := by
    filter_upwards [hz.comp_tendsto hneg] with x hx
    change localInverseAmplitude m B j (-x) = 0 at hx
    simp only [antipodalConjugate,hx,star_zero]
  rw [actualStationaryCoefficient_local m h e heq]
  exact actualStationaryCoefficient_zero_amplitude m h e

end Falconer

end OAI
