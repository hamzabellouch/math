import OAI.Probability.SLE.Loewner.SlitChartExteriorComparison

namespace OAI

/-! A common interior base point for normalized forward charts of bounded slits. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma radiusHullMap_two_radius {R : ℝ} (hR : 0<R) :
    radiusHullMap R (((2*R:ℝ):ℂ)*I)=((3*R/2:ℝ):ℂ)*I := by
  rw [radiusHullMap_formula hR]
  have hr : (R:ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  push_cast
  field_simp [hr,Complex.I_ne_zero]
  ring_nf
  norm_num [Complex.I_sq]

lemma SimpleSlitChart.vertical_base_bounds {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖≤R) :
    3*R/2≤(P.forward (((2*R:ℝ):ℂ)*I)).im ∧
      ‖P.forward (((2*R:ℝ):ℂ)*I)‖≤3*R := by
  have hn : ‖((2*R:ℝ):ℂ)*I‖=2*R := by
    simp [abs_of_pos hR]
  have hzH : (((2*R:ℝ):ℂ)*I)∈upperHalfPlane := by
    change 0<(((2*R:ℝ):ℂ)*I).im
    simpa using mul_pos (by norm_num : (0:ℝ)<2) hR
  have hz : (((2*R:ℝ):ℂ)*I)∈exteriorUpperRadius R :=
    ⟨by rw [hn]; linarith,hzH⟩
  have hh := P.exterior_comparison hR hp hz
  rw [radiusHullMap_two_radius hR] at hh
  have him : (((3*R/2:ℝ):ℂ)*I).im=3*R/2 := by simp
  rw [him] at hh
  refine ⟨hh.1,?_⟩
  have hd : 0<3*R/2 := by positivity
  have he := (le_div_iff₀ hd).mp hh.2
  have hnorm : ‖((3*R/2:ℝ):ℂ)*I‖=3*R/2 := by simp [abs_of_pos hR]
  have htri := norm_le_norm_sub_add (P.forward (((2*R:ℝ):ℂ)*I)) (((3*R/2:ℝ):ℂ)*I)
  rw [hnorm] at htri
  have hc := P.capacity_pos
  nlinarith

end SLEExactGauge

end

end OAI
