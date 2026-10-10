import Mathlib
import OAI.Probability.Perceptron.Cavity.CavitySmoothLimit
import OAI.Probability.Perceptron.Variational.CompactEnvelope
import OAI.Probability.Perceptron.Pressure.PressureMonotone

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem expectedPressure_limit_terminal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (f : ℝ→ᵇℝ) :
    Tendsto (fun n : ℕ=>expectedPressure α 1 f (n+1)) atTop
      (𝓝 (terminalVariational P α f).toReal) := by
  obtain ⟨g,gs,gn,gl,gc⟩:=exists_smooth_lower_sequence f
  obtain ⟨h,hs,hn,hl,hc⟩:=exists_smooth_upper_sequence f
  have gV:=controlValue_uniform_of_compact P hB f (fun n=>(g n).f) (‖f‖+1)
    (by positivity) (by linarith) gn gc
  have hV:=controlValue_uniform_of_compact P hB f (fun n=>(h n).f) (‖f‖+1)
    (by positivity) (by linarith) hn hc
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hδ : 0<ε/(4*α):=by positivity
  obtain ⟨G,hG⟩:=gV _ hδ
  obtain ⟨H,hH⟩:=hV _ hδ
  have hGV:=terminalVariational_abs_sub_le P α hα.le (g G).f f (ε/(4*α))
    (fun m=>(hG G le_rfl m).le)
  have hHV:=terminalVariational_abs_sub_le P α hα.le (h H).f f (ε/(4*α))
    (fun m=>(hH H le_rfl m).le)
  have he : α*(ε/(4*α))=ε/4 := by field_simp
  rw [he] at hGV hHV
  have hg:=expectedPressure_limit_smooth P hB hα (g G) (gs G).1 (gs G).2.1 (gs G).2.2
  have hh:=expectedPressure_limit_smooth P hB hα (h H) (hs H).1 (hs H).2.1 (hs H).2.2
  filter_upwards [Metric.tendsto_nhds.1 hg (ε/4) (by positivity),
    Metric.tendsto_nhds.1 hh (ε/4) (by positivity)] with n hgn hhn
  have hlo:=expectedPressure_mono_terminal α (g G).f f (gl G) n
  have hhi:=expectedPressure_mono_terminal α f (h H).f (hl H) n
  rw [Real.dist_eq] at hgn hhn ⊢
  rcases abs_le.mp hGV with ⟨glo,ghi⟩
  rcases abs_le.mp hHV with ⟨hlo',hhi'⟩
  rcases abs_lt.mp hgn with ⟨gln,ghn⟩
  rcases abs_lt.mp hhn with ⟨hln,hhn⟩
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
end SphericalPerceptronFreeEnergy

end

end OAI
