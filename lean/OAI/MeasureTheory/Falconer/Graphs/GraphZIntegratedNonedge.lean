import OAI.MeasureTheory.Falconer.Graphs.GraphZNonedgeScale
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_phase_amplitude_continuous {f : (Plane × ℝ) → ℂ}
    (hf : Continuous f) (R s : ℝ) (x y : Plane) :
    Continuous (fun q : Plane × ℝ =>
      Complex.exp (Complex.I*Complex.ofReal (R*inner ℝ q.1
        (graphA q.2 x+s • graphB q.2 y)))*f q) := by
  apply Continuous.mul _ hf
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  apply continuous_const.mul
  apply continuous_fst.inner
  unfold graphA graphB
  fun_prop

theorem graph_z_integrated_nonedge_bound {f : (Plane × ℝ) → ℂ} {C : ℝ}
    (n N : ℕ) (sig v p s : ℝ) (x y : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hτ : ∀ η : Plane, (∃ z, f (η,z) ≠ 0) →
      ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/16 ≤
        |(2:ℝ)^v*inner ℝ η (graphDerivative s x y)|) :
    ‖∫ z : ℝ, ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      (8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ))) *
        volume.real (Metric.closedBall (0:Plane) 8) := by
  let F : Plane → ℝ → ℂ := fun η z => Complex.exp (Complex.I*Complex.ofReal
    ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)
  have hc : Continuous F.uncurry :=
    graph_phase_amplitude_continuous (hf.global_smooth hs).continuous _ _ _ _
  have hcompact : HasCompactSupport f :=
    graphAmplitudeCompact_isCompact.of_isClosed_subset isClosed_closure hs
  have hFc : HasCompactSupport F.uncurry := hcompact.mul_left
  have hswap := integral_integral_swap_of_hasCompactSupport hc hFc
    (μ := (volume : Measure Plane)) (ν := (volume : Measure ℝ))
  change ‖∫ z, ∫ η, F η z‖ ≤ _
  rw [← hswap]
  have hzero (η : Plane) (hη : η ∉ Metric.closedBall (0:Plane) 8) :
      (∫ z, F η z) = 0 := by
    have hz (z : ℝ) : f (η,z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hη (hs hm).1.1
    simp [F,hz]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hb (η : Plane) : ‖∫ z, F η z‖ ≤
      8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
    by_cases hn : ∃ z, f (η,z) ≠ 0
    · exact graph_z_nonedge_scale_bound n N sig v p s x y η hf hs hC (hτ η hn)
    · have hz (z : ℝ) : f (η,z) = 0 := by simpa using not_exists.mp hn z
      simp only [F,hz,mul_zero,integral_zero,norm_zero]
      positivity
  have : Fact (volume (Metric.closedBall (0:Plane) 8) < ⊤) :=
    ⟨(isCompact_closedBall (0:Plane) 8).measure_lt_top⟩
  have he := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Metric.closedBall (0:Plane) 8))
    (Filter.Eventually.of_forall hb)
  simpa only [Measure.real,Measure.restrict_apply_univ] using he

end PlanarFalconer

end OAI
