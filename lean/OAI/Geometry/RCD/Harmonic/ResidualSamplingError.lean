import OAI.Geometry.RCD.Transport.GeodesicProductSamples

namespace OAI

/-! # Choosing the finite sampling accuracy

The number of samples is fixed first. Only then is the product
approximation error chosen. The needed error has a square-root rate.
-/

open Filter Topology
noncomputable section
namespace RegularPointCoordinates

def residualSamplingError (m : ℕ) (ε : ℝ) : ℝ :=
  3*ε/(m:ℝ)+ε+2*Real.sqrt (14*ε*((1/4:ℝ)+7*ε))

theorem residualSamplingError_tendsto (m : ℕ) :
    Tendsto (residualSamplingError m) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (residualSamplingError m) := by unfold residualSamplingError; fun_prop
  simpa [residualSamplingError] using hc.continuousAt.tendsto (x := (0:ℝ))

theorem exists_residual_sampling_accuracy {m : ℕ} (hm : 0 < m) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ c ∧ residualSamplingError m ε ≤ a/(2*m) := by
  have ht : 0 < a/(2*(m:ℝ)) := by positivity
  have he := (residualSamplingError_tendsto m).eventually (gt_mem_nhds ht)
  obtain ⟨d,hd,hdmem⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min d c/2,by positivity,?_,?_⟩
  · have hmc := min_le_right d c
    linarith [lt_min hd hc]
  · apply le_of_lt
    apply hdmem
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < min d c/2)]
    have hmd := min_le_left d c
    linarith [lt_min hd hc]

theorem residualSamplingError_bounds {m : ℕ} {ε D : ℝ}
    (he : 0 ≤ ε) (hD : D ≤ 1/4) :
    3*ε/(m:ℝ)+ε+2*Real.sqrt (14*ε*(D+7*ε)) ≤ residualSamplingError m ε := by
  unfold residualSamplingError
  gcongr

end RegularPointCoordinates

end

end OAI
