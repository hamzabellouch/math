import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowVelocityBounds

namespace OAI

/-! Mean-zero forcing, classical uniqueness, and bounded energy for the
initialized logarithmic slowdown. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal
open ShearFlows

namespace ForcedComputation

theorem slowFromRest_force_zero {V : Velocity}
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (ν : ℝ) {t : ℝ} (ht : t < (1 / 64 : ℝ)) (x : Space) :
    force ν (slowFromRest V) (t, x) = 0 := by
  have he : slowFromRest V =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
    filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_lt_nhds ht)] with y hy
    exact slowFromRest_zero_collar hzero hy y.2
  rw [force_congr_germ he ν]
  rw [force_eq_mixed (contDiff_const : ContDiff ℝ ∞ (fun _ : SpaceTime => (0 : Space)))]
  simp only [mixedDerivative_zero, Finset.sum_const_zero, smul_zero, sub_zero]

theorem slowFromRest_force_mean_zero {L : ℝ} (hL : 0 ≤ L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hper : SpatiallyPeriodic L V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (ha : ZeroAdvection V) (hm : HasZeroMean L V) (hm0 : HasZeroMean L (force 0 V))
    (ν : ℝ) : HasZeroMean L (force ν (slowFromRest V)) := by
  have hd : HasZeroMean L (fun y => laplacian (fun x => V (y.1, x)) y.2) :=
    laplacian_mean_zero hL hV hper
  intro t
  by_cases ht : t < 0
  · simp_rw [slowFromRest_force_zero hzero ν (by linarith : t < (1 / 64 : ℝ))]
    simp
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    have he (x : Space) : force ν (slowFromRest V) (t, x) =
        (1 + t)⁻¹ ^ 2 • force 0 V (logClock t, x) -
        (1 + t)⁻¹ ^ 2 • V (logClock t, x) -
        ν • ((1 + t)⁻¹ • laplacian (fun y => V (logClock t, y)) x) := by
      rw [slowFromRest_force_eq hV hzero ha ν (by linarith)]
      simp only [slowForce, quadraticPhase, viscousPhase, logarithmicProfile,
        ha (Real.log (1 + t)) x, add_zero, pow_one, smul_sub, force, zero_smul, sub_zero, logClock]
    simp_rw [he]
    have hi0 : IntegrableOn (fun x => force 0 V (logClock t, x)) (fundamentalCube L) :=
      ((force_smooth hV 0).continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
    have hi : IntegrableOn (fun x => V (logClock t, x)) (fundamentalCube L) :=
      (hV.continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
    have hiD : IntegrableOn (laplacian (fun x => V (logClock t, x))) (fundamentalCube L) :=
      ((laplacian_smooth hV).continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
    have hiL : IntegrableOn (fun x => (1 + t)⁻¹ ^ 2 • force 0 V (logClock t, x) -
        (1 + t)⁻¹ ^ 2 • V (logClock t, x)) (fundamentalCube L) :=
      (hi0.smul ((1 + t)⁻¹ ^ 2)).sub (hi.smul ((1 + t)⁻¹ ^ 2))
    have hiR : IntegrableOn (fun x => ν • ((1 + t)⁻¹ •
        laplacian (fun y => V (logClock t, y)) x)) (fundamentalCube L) :=
      (hiD.smul ((1 + t)⁻¹)).smul ν
    have hiA : IntegrableOn (fun x => (1 + t)⁻¹ ^ 2 • force 0 V (logClock t, x))
        (fundamentalCube L) := hi0.smul ((1 + t)⁻¹ ^ 2)
    have hiB : IntegrableOn (fun x => (1 + t)⁻¹ ^ 2 • V (logClock t, x))
        (fundamentalCube L) := hi.smul ((1 + t)⁻¹ ^ 2)
    rw [integral_sub hiL hiR, integral_sub hiA hiB]
    simp only [integral_smul, hm0 (logClock t), hm (logClock t), hd (logClock t), smul_zero, sub_zero]

theorem slowFromRest_unique {L ν : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {V : Velocity} (hV : ContDiff ℝ ∞ V) (hper : SpatiallyPeriodic L V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hdiv : Solenoidal V) (ha : ZeroAdvection V) {K : ℝ≥0}
    (hK : ∀ t, LipschitzWith K (fun x => V (t, x))) :
    ∀ u p, IsClassicalSolution L ν (force ν (slowFromRest V)) u p →
      ∀ t, 0 ≤ t → ∀ x, u (t, x) = slowFromRest V (t, x) ∧ p (t, x) = 0 := by
  have hsol := slowFromRest_solution hV hper hzero hdiv ha ν
  have hb (t : ℝ) (_ : 0 ≤ t) (x : Space) :
      ‖fderiv ℝ (fun y => slowFromRest V (t, y)) x‖ ≤ (K : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (slowFromRest_lipschitz hK t)
  intro u p hu
  have he := classical_velocity_unique hL hν hu hsol hb
  have hp := classical_pressure_unique hL hu hsol he
  exact fun t ht x => ⟨he t ht x, hp t ht x⟩

theorem slowFromRest_energy {L : ℝ} {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (hb : BoundedMixedDerivatives V) :
    ∃ E : ℝ, ∀ t, kineticEnergy L (slowFromRest V) t ≤ E := by
  obtain ⟨B, hB, hbound⟩ := hb []
  exact ⟨(1 / 2 : ℝ) * volume.real (fundamentalCube L) * (3 * B ^ 2),
    fun t => kineticEnergy_bound (slowFromRest_smooth hV hzero).continuous L hB
      (fun y => slowFromRest_uniform_bound hB hbound y) t⟩

end ForcedComputation

end

end OAI
