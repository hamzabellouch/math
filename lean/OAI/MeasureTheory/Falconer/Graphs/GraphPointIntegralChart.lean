import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeIntegralErrors

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphTransport_eq_point_phase (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    {η : Plane} (hη : η ∈ graphPlaneSlit) (z : ℝ) :
    graphTransport (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ ((2:ℝ)^v) (graphSourceChartAxis distance plus) (z,η) =
      Complex.exp (Complex.I*Complex.ofReal ((2:ℝ)^v*inner ℝ η
        (graphA z (x 0-x 1)+graphSourceSign distance plus • graphB z (x 2-x 3)))) *
        graphAmplitudePullback b x distance plus axis δ j k Ψ (η,z) := by
  cases distance <;> cases plus <;>
    simp only [graphTransport,graphAmplitudePullback,graphShellJacobian,
      graphSourceChartAxis,graphSourceSign,Bool.false_eq_true,↓reduceIte,add_zero,one_smul,
      neg_one_smul,← sub_eq_add_neg] <;>
    first | rw [graphFourKernel_phase_plus b _ x hη] | rw [graphFourKernel_phase_minus b _ x hη]
  all_goals simp only [Complex.real_smul,Complex.ofReal_mul]; ring_nf

theorem graphTransport_integral_eq_pointIntegral (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    (hi : Integrable (graphTransport
      (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ ((2:ℝ)^v) (graphSourceChartAxis distance plus))) :
    (∫ p : ℝ × Plane, graphTransport
      (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ ((2:ℝ)^v) (graphSourceChartAxis distance plus) p) =
    graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j k Ψ)
      v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards [graphPlaneSlit_ae_eq_univ] with η hη
  exact graphTransport_eq_point_phase b x distance plus axis δ v j k Ψ (hη.mpr (mem_univ η)) z

end PlanarFalconer

end OAI
