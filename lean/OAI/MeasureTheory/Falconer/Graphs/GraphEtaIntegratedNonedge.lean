import OAI.MeasureTheory.Falconer.Graphs.GraphEtaNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_eta_nonedge_scale_bound {f : (Plane × ℝ) → ℂ} {C : ℝ} (n N : ℕ)
    (sig v p s z : ℝ) (x y : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hq : ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/2 ≤
      ‖((2:ℝ)^v) • (graphA z x+s • graphB z y)‖) :
    ‖∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  let q := ((2:ℝ)^v) • (graphA z x+s • graphB z y)
  let G := (2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))
  let E := graphNonedgeDerivativeScale N sig (v-p)
  have hG : 0 < G := by dsimp [G]; positivity
  have hE : 0 < E := by dsimp [E,graphNonedgeDerivativeScale]; positivity
  have hqpos : 0 < ‖q‖ := (by positivity : 0 < G/2).trans_le hq
  have hqne : q ≠ 0 := norm_pos_iff.mp hqpos
  have he := graph_eta_nonstationary_bound n hf hs hC hE.le ((2:ℝ)^v) s z x y hqne
  have hratio : E/‖q‖ ≤ 2*((2:ℝ)^N)^(-26*sig) := by
    calc
      _ ≤ E/(G/2) := div_le_div_of_nonneg_left hE.le (by positivity) hq
      _ = 2*(E/G) := by field_simp
      _ = _ := by rw [graph_nonedge_scale_gain]
  calc
    _ ≤ (C*E^n*volume.real (Metric.closedBall (0:Plane) 8))/‖q‖^n := he
    _ = (C*volume.real (Metric.closedBall (0:Plane) 8))*(E/‖q‖)^n := by
      rw [div_pow]; ring
    _ ≤ (C*volume.real (Metric.closedBall (0:Plane) 8))*(2*((2:ℝ)^N)^(-26*sig))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio _) (by positivity)
    _ = C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
      ring

theorem graph_eta_integrated_nonedge_bound {f : (Plane × ℝ) → ℂ} {C : ℝ}
    (n N : ℕ) (sig v p s : ℝ) (x y : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hq : ∀ z : ℝ, (∃ η, f (η,z) ≠ 0) →
      ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/2 ≤
        ‖((2:ℝ)^v) • (graphA z x+s • graphB z y)‖) :
    ‖∫ z : ℝ, ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      8*C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  let F : ℝ → ℂ := fun z => ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
    ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)
  have hzero (z : ℝ) (hz : z ∉ Icc (-4:ℝ) 4) : F z = 0 := by
    have he (η : Plane) : f (η,z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hz (hs hm).1.2
    simp [F,he]
  have hb (z : ℝ) : ‖F z‖ ≤
      C*volume.real (Metric.closedBall (0:Plane) 8)*2^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
    by_cases hn : ∃ η, f (η,z) ≠ 0
    · exact graph_eta_nonedge_scale_bound n N sig v p s z x y hf hs hC (hq z hn)
    · have hz (η : Plane) : f (η,z) = 0 := by simpa using not_exists.mp hn η
      simp only [F,hz,mul_zero,integral_zero,norm_zero]
      positivity
  change ‖∫ z, F z‖ ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have he := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (s := Icc (-4:ℝ) 4) (by simp) (Filter.Eventually.of_forall hb)
  apply he.trans_eq
  simp [Measure.real,Real.volume_Icc]
  ring

end PlanarFalconer

end OAI
