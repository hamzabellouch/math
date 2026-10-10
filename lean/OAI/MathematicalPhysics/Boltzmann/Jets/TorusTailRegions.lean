import OAI.MathematicalPhysics.Boltzmann.Branching.CommonMomentEnvelope

namespace OAI

/-! # Vanishing small-annulus collision bounds on the spatial torus -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.AnnularEnvelope

instance (T : ℝ) : IsFiniteMeasure (timePositionVolume T) := by
  dsimp [timePositionVolume]
  infer_instance

def torusTail (s₀ η : ℝ) (J : ℕ) : Set (ℝ × Position) :=
  torusChart ⁻¹' tailRegion s₀ η J

theorem torusTail_measurable (s₀ η : ℝ) (J : ℕ) : MeasurableSet (torusTail s₀ η J) :=
  (tailRegion_measurable s₀ η J).preimage torusChart_measurable

theorem torus_tail_integral_tendsto {s₀ η T : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {G : ℝ × Position → ℝ} (hG : Integrable G (timePositionVolume T)) :
    Tendsto (fun J => ∫ u in torusTail s₀ η J, G u ∂timePositionVolume T) atTop (𝓝 0) := by
  have hm (J) : AEStronglyMeasurable ((torusTail s₀ η J).indicator G) (timePositionVolume T) :=
    hG.aestronglyMeasurable.indicator (torusTail_measurable s₀ η J)
  have hb (J) : ∀ᵐ u ∂timePositionVolume T, ‖(torusTail s₀ η J).indicator G u‖ ≤ ‖G u‖ :=
    ae_of_all _ (fun u => norm_indicator_le_norm_self G u)
  have ht : ∀ᵐ u ∂timePositionVolume T,
      Tendsto (fun J => (torusTail s₀ η J).indicator G u) atTop (𝓝 0) := by
    filter_upwards [] with u
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_outside_tail hs₀ hη (torusChart u)] with J hJ
    exact (indicator_of_notMem (show u ∉ torusTail s₀ η J from hJ) G).symm
  simpa only [integral_indicator (torusTail_measurable s₀ η _),integral_zero] using
    tendsto_integral_of_dominated_convergence (fun u => ‖G u‖) hm hG.norm hb ht

theorem torus_tail_lintegral_tendsto {s₀ η T : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {G : ℝ × Position → ℝ} (hG : Integrable G (timePositionVolume T)) (hGn : ∀ u, 0 ≤ G u) :
    Tendsto (fun J => ∫⁻ u in torusTail s₀ η J, ENNReal.ofReal (G u) ∂timePositionVolume T)
      atTop (𝓝 0) := by
  have he (J) : (∫⁻ u in torusTail s₀ η J, ENNReal.ofReal (G u) ∂timePositionVolume T) =
      ENNReal.ofReal (∫ u in torusTail s₀ η J, G u ∂timePositionVolume T) :=
    (ofReal_integral_eq_lintegral_ofReal hG.restrict (ae_of_all _ hGn)).symm
  simp_rw [he]
  simpa only [Function.comp_def,ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (torus_tail_integral_tendsto hs₀ hη hG)

theorem common_collision_tail_tendsto {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) (A B : ℝ) :
    Tendsto (fun J => ∫⁻ u in torusTail s₀ η J,
      ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2) ∂timePositionVolume T)
        atTop (𝓝 0) :=
  torus_tail_lintegral_tendsto hs₀.le hη.le
    ((torus_common_square_integrable hs₀ hη hηmax hT A B).const_mul 3)
    (fun _ => mul_nonneg (by norm_num) (sq_nonneg _))

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
