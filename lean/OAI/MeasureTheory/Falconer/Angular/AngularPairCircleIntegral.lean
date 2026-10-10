import OAI.MeasureTheory.Falconer.Angular.AngularCellSpatialIntegral
import OAI.MeasureTheory.Falconer.Angular.ActualTwoPointStationary
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def angularPairCircleIntegral (β : Plane → UnitCircle → ℂ)
    (x y : Plane) (r : ℝ) : ℂ :=
  ∫ u, sourcePlaneWave r u (x-y) * (β x u*conj (β y u)) ∂sourceArcLength

 theorem angular_four_kernel_pair_integral (β γ : Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (r : ℝ) :
    (∫ u, ∫ w, graphFourKernel ![β,β,γ,γ] (fun _ => 1) x r u w
      ∂sourceArcLength ∂sourceArcLength) =
      angularPairCircleIntegral β (x 0) (x 1) r * angularPairCircleIntegral γ (x 2) (x 3) r := by
  have he (u w : UnitCircle) : graphFourKernel ![β,β,γ,γ] (fun _ => 1) x r u w =
      (sourcePlaneWave r u (x 0-x 1)*(β (x 0) u*conj (β (x 1) u))) *
      (sourcePlaneWave r w (x 2-x 3)*(γ (x 2) w*conj (γ (x 3) w))) := by
    simp only [graphFourKernel,graphFourAmplitude,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    ring
  simp_rw [he,integral_const_mul,integral_mul_const]
  rfl

 theorem angularCellSpatialIntegral_pair (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (row col : CellPath × CellPath) (v : ℝ) (Ψ : ℝ → ℝ) :
    angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ =
      ∫ x, ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
        (angularPairCircleIntegral β (x 0) (x 1) r * angularPairCircleIntegral γ (x 2) (x 3) r))
      ∂Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict
        (![ (Q₁.descendant row.1).carrier, (Q₁.descendant col.1).carrier,
            (Q₂.descendant row.2).carrier, (Q₂.descendant col.2).carrier] i)) := by
  simp only [angularCellSpatialIntegral,integral_smul,angular_four_kernel_pair_integral]

 theorem angularPairCircleIntegral_cosine (β : Plane → UnitCircle → ℂ)
    (hβ : ∀ x, Continuous (β x)) (x y : Plane) (r θ₀ : ℝ)
    (hangle : x-y = ‖x-y‖ • sourceDirection θ₀) :
    angularPairCircleIntegral β x y r =
      ∫ θ in (-Real.pi)..Real.pi, cosineOscillator (r*‖x-y‖) (θ-θ₀) *
        (β x (sourceUnitDirection θ)*conj (β y (sourceUnitDirection θ))) := by
  have hm : Measurable (fun u => sourcePlaneWave r u (x-y)*(β x u*conj (β y u))) := by
    apply Measurable.mul
    · exact ((sourcePlaneWave_continuous (x-y)).comp (continuous_const.prodMk continuous_id)).measurable
    · exact (hβ x).measurable.mul (Complex.continuous_conj.measurable.comp (hβ y).measurable)
  rw [angularPairCircleIntegral,sourceArcLength_integral_period hm.aestronglyMeasurable]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  congr 1
  have he : inner ℝ (sourceDirection θ) (x-y) = ‖x-y‖*Real.cos (θ-θ₀) := by
    calc
      _ = inner ℝ (sourceDirection θ) (‖x-y‖ • sourceDirection θ₀) :=
        congrArg (inner ℝ (sourceDirection θ)) hangle
      _ = _ := by rw [inner_smul_right,inner_sourceDirection]
  change Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection θ) (x-y):ℂ)) = _
  rw [he]
  simp only [cosineOscillator,Complex.ofReal_mul]
  congr 1
  ring

end PlanarFalconer

end OAI
