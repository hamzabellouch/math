import OAI.MeasureTheory.Falconer.Geometry.ProjectionSinc
import OAI.MeasureTheory.Falconer.Radial.RadialIntervalEnergy

namespace OAI

/-! # Averaged projection collisions from the half-dimensional Fourier bound -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projection_collision_lintegral_band : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) (ε H : ℝ),
      0 < ε → 0 ≤ H → 100/ε ≤ 2*Real.pi*H →
      projectionCollision μ w ε ≤ ENNReal.ofReal (C*ε)*
        ∫⁻ r : ℝ in Icc (-H) H, ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := projection_collision_band (d := d)
  refine ⟨C*(2*Real.pi)/100,by positivity,?_⟩
  intro μ _ w ε H hε hH hscale
  have hA : 0 < 100/ε := by positivity
  have h := hbound μ w (100/ε) H hA hH hscale
  have hw : 100/(100/ε) = ε := by field_simp
  rw [hw] at h
  have hi : IntegrableOn (fun r : ℝ => ‖PlanarFalconer.sourceFourier μ (r • w)‖^2)
      (Icc (-H) H) := by
    have hc : Continuous (fun r : ℝ => ‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := by
      unfold PlanarFalconer.sourceFourier
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hr : (projectionCollision μ w ε).toReal ≤ (C*(2*Real.pi)/100*ε)*
      ∫ r in Icc (-H) H, ‖PlanarFalconer.sourceFourier μ (r • w)‖^2 := by
    apply (le_of_mul_le_mul_left _ hA)
    calc
      _ ≤ C*(2*Real.pi)*(∫ r in Icc (-H) H, ‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := h
      _ = _ := by field_simp
  have hp : projectionCollision μ w ε ≠ ∞ := measure_ne_top (μ.prod μ) _
  rw [← ENNReal.ofReal_toReal hp]
  have hh := ENNReal.ofReal_le_ofReal hr
  rwa [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with r; positivity)] at hh

theorem averaged_projection_collision : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ]
      (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (D R K L : ℝ),
      0 ≤ D → (∀ᵐ x ∂μ, ‖x‖ ≤ D) → ∀ n : ℕ, (2:ℝ)^n ≤ R → 1 ≤ K → 1 ≤ L →
      ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (K*r^((d:ℝ)/2))) →
      (∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^((d:ℝ)/2))) →
      ∀ ε : ℝ, 0 < ε → 100/ε ≤ 2*Real.pi*((2:ℝ)^n) →
      (∫⁻ w : Sphere d, projectionCollision μ (w:Space d) ε ∂ν) ≤
        ENNReal.ofReal (C*ε*(2+(n:ℝ)*(halfDimensionalShellConstant d*
          (Real.exp ((Real.pi^2/2)*D^2))^2*K*L))) := by
  obtain ⟨C,hC,hpoint⟩ := projection_collision_lintegral_band (d := d)
  refine ⟨C,hC,?_⟩
  intro μ _ ν _ D R K L hD hsupport n hR hK hL hmass hμ hν ε hε hscale
  calc
    _ ≤ ∫⁻ w : Sphere d, ENNReal.ofReal (C*ε)*
        (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν :=
      lintegral_mono (fun w => hpoint μ (w:Space d) ε ((2:ℝ)^n) hε (by positivity) hscale)
    _ = ENNReal.ofReal (C*ε)*(∫⁻ w : Sphere d,
        (∫⁻ r : ℝ in Icc (-((2:ℝ)^n)) ((2:ℝ)^n),
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier μ (r • (w:Space d))‖^2)) ∂ν) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C*ε)*ENNReal.ofReal (2+(n:ℝ)*(halfDimensionalShellConstant d*
        (Real.exp ((Real.pi^2/2)*D^2))^2*K*L)) :=
      mul_le_mul_right (dyadic_half_dimensional_average μ ν hD hsupport n hR hK hL hmass hμ hν) _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end Falconer

end OAI
