import OAI.MeasureTheory.Falconer.Angular.AngularTransformSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable def sourcePlaneWave (r : ℝ) (ω : UnitCircle) (x : Plane) : ℂ :=
  Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ))

theorem sourcePlaneWave_norm (r : ℝ) (ω : UnitCircle) (x : Plane) :
    ‖sourcePlaneWave r ω x‖ = 1 := by
  simpa only [sourcePlaneWave, mul_one, norm_one] using angular_integrand_norm r ω x (fun _ _ => 1)

theorem sourcePlaneWave_sub (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    sourcePlaneWave r ω x * conj (sourcePlaneWave r ω y) =
      sourcePlaneWave r ω (x-y) := by
  simp only [sourcePlaneWave, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add, inner_sub_right, Complex.ofReal_sub]
  congr 1
  ring

noncomputable def sourceDistanceF (ψ : UnitCircle → ℂ)
    (U V : ℝ × UnitCircle → ℂ) (r : ℝ) : ℂ :=
  ∫ ω, ψ ω * U (r,ω) * conj (V (r,ω)) ∂sourceArcLength

noncomputable def sourceDistanceHF (a v : ℝ) (Ψ : ℝ → ℝ)
    (ψ : UnitCircle → ℂ) (U V : ℝ × UnitCircle → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(2*(v-a))) *
    ∫⁻ r, ‖sourceDistanceF ψ U V r‖ₑ^2 ∂sourceAngularShellMeasure v Ψ

theorem measurable_sourceDistanceF (ψ : UnitCircle → ℂ)
    (U V : ℝ × UnitCircle → ℂ) (hψ : Measurable ψ)
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (sourceDistanceF ψ U V) := by
  exact (((hψ.comp measurable_snd).mul hU).mul
    (Complex.continuous_conj.measurable.comp hV)).stronglyMeasurable.integral_prod_right'.measurable

theorem sourceAngularTransform_product (ρ ν : Measure Plane) (X Y : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ X M₁ b₁ r ω *
      conj (sourceAngularTransform ν Y M₂ b₂ r ω) =
    (M₁*M₂)⁻¹ • (∫ x in X, ∫ y in Y,
      sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω)) ∂ν ∂ρ) := by
  have he (x y : Plane) :
      sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω)) =
      (sourcePlaneWave r ω x * b₁ x ω) * conj (sourcePlaneWave r ω y * b₂ y ω) := by
    rw [← sourcePlaneWave_sub, map_mul]
    ring
  simp_rw [he, integral_const_mul, integral_mul_const, integral_conj]
  simp only [sourceAngularTransform, sourcePlaneWave, Complex.real_smul,
    map_mul, Complex.conj_ofReal, mul_inv_rev, Complex.ofReal_mul]
  ring

end PlanarFalconer

end OAI
