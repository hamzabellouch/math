import OAI.MeasureTheory.Falconer.Angular.AngularEnvelope
import OAI.MeasureTheory.Falconer.Angular.SharedAngular

namespace OAI

/-! # Separating the two original regularized profiles

Cauchy--Schwarz uses the same radial shell measure on both sides and keeps
exactly the common dimension-dependent normalization. Each resulting
energy duplicates one original endpoint law, cell and symbol.
-/

namespace Falconer
open Set MeasureTheory

 theorem independentAngularEnergy_sq_le_self {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hUC : ∀ z, ‖U z‖ ≤ C) (hVD : ∀ z, ‖V z‖ ≤ D) :
    (independentAngularEnergy a v Ψ U V)^2 ≤
      independentAngularEnergy a v Ψ U U * independentAngularEnergy a v Ψ V V := by
  have hUU := independentAngularIntegrand_integrable v Ψ U U hU hU hC hC hUC hUC
  have hVV := independentAngularIntegrand_integrable v Ψ V V hV hV hD hD hVD hVD
  have hUV := independentAngularIntegrand_integrable v Ψ U V hU hV hC hD hUC hVD
  have h := real_integral_product_sq_le (PlanarFalconer.sourceAngularShellMeasure v Ψ)
    (sphereMoment U) (sphereMoment V) (by simpa only [pow_two] using hUU)
    (by simpa only [pow_two] using hVV) hUV
  unfold independentAngularEnergy
  calc
    _ = ((2:ℝ)^((d:ℝ)*(v-a)))^2 *
        (∫ r, sphereMoment U r * sphereMoment V r
          ∂PlanarFalconer.sourceAngularShellMeasure v Ψ)^2 := mul_pow _ _ _
    _ ≤ ((2:ℝ)^((d:ℝ)*(v-a)))^2 *
        ((∫ r, (sphereMoment U r)^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) *
          (∫ r, (sphereMoment V r)^2 ∂PlanarFalconer.sourceAngularShellMeasure v Ψ)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by simp only [pow_two]; ring

 theorem independentAngularEnergy_le_self_sqrt {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hUC : ∀ z, ‖U z‖ ≤ C) (hVD : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V ≤
      Real.sqrt (independentAngularEnergy a v Ψ U U) *
        Real.sqrt (independentAngularEnergy a v Ψ V V) := by
  simpa only [Real.sqrt_mul (independentAngularEnergy_nonneg a v Ψ U U)] using
    Real.le_sqrt_of_sq_le (independentAngularEnergy_sq_le_self a v Ψ U V hU hV hC hD hUC hVD)

 theorem angularEnvelope_two_profile {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight ≤
      Real.sqrt (angularEnvelope μ μ M M k D a v Ψ GoodLeft GoodLeft) *
        Real.sqrt (angularEnvelope ν ν P P k D a v Ψ GoodRight GoodRight) := by
  apply csSup_le (angularEnergyValues_nonempty μ ν M P k D a v Ψ GoodLeft GoodRight)
  intro H hH
  rcases hH with rfl | ⟨b,c,hb,hc,rfl⟩
  · positivity
  let U := fun z : ℝ × Sphere (n+2) => endpointTransform μ M b z.1 z.2
  let V := fun z : ℝ × Sphere (n+2) => endpointTransform ν P c z.1 z.2
  have hU : Measurable U := measurable_endpointTransform μ M b hb.1.measurable
  have hV : Measurable V := measurable_endpointTransform ν P c hc.1.measurable
  have hUC (z : ℝ × Sphere (n+2)) : ‖U z‖ ≤ μ.real univ/M := by
    simpa only [one_mul] using endpointTransform_norm_le μ hM b hb.1.bound z.1 z.2
  have hVD (z : ℝ × Sphere (n+2)) : ‖V z‖ ≤ ν.real univ/P := by
    simpa only [one_mul] using endpointTransform_norm_le ν hP c hc.1.bound z.1 z.2
  have hu := admissible_energy_le_angularEnvelope μ μ hM hM k D a v Ψ GoodLeft GoodLeft b b hb hb
  have hv := admissible_energy_le_angularEnvelope ν ν hP hP k D a v Ψ GoodRight GoodRight c c hc hc
  exact (independentAngularEnergy_le_self_sqrt a v Ψ U V hU hV
    (div_nonneg measureReal_nonneg hM.le) (div_nonneg measureReal_nonneg hP.le) hUC hVD).trans
      (mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Falconer

end OAI
