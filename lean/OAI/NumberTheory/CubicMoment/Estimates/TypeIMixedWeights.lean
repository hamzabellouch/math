import OAI.NumberTheory.CubicMoment.Estimates.ShortConvolutionTypeI

namespace OAI

/-! The actual mixed-term weight from the corrected square. The factor
`(Na)^(-1/6)` is transferred to a fixed smooth test function and the
squarefree model is retained without removing mutual coprimality. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def typeIMixedGauss (r : Eisenstein) (W : ℝ → ℂ) (U : ℝ) : ℂ :=
  ∑' u : PrimaryArgument, gauss (r*u)*((norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U)

def typeIMixedModel (r : Eisenstein) (W : ℝ → ℂ) (U : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u then (idealMoebius (r*u):ℂ)^2*
    ((cStar*norm (r*u)^(-1/6:ℝ)*norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) else 0

private lemma typeIMixed_power_scale {n U : ℝ} (hn : 0 ≤ n) (hU : 0 < U) :
    U^(-1/6:ℝ)*(n/U)^(-1/6:ℝ) = n^(-1/6:ℝ) := by
  rw [Real.div_rpow hn hU.le]
  have hne : U^(-1/6:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hU _)
  field_simp

lemma typeIMixedGauss_eq (r : Eisenstein) (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) :
    typeIMixedGauss r W U = ((U^(-1/6:ℝ):ℝ):ℂ)*
      metaplecticAngularSmoothSum r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U 0 := by
  rw [typeIMixedGauss,metaplecticAngularSmoothSum,←tsum_mul_left]
  apply tsum_congr
  intro u
  have hs := congrArg (fun x : ℝ => (x:ℂ)) (typeIMixed_power_scale (norm_nonneg u) hU)
  push_cast at hs
  simp only [theta,zpow_zero,mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
  calc
    _ = gauss (r*u)*( ((U^(-1/6:ℝ):ℝ):ℂ)*(((norm u/U)^(-1/6:ℝ):ℝ):ℂ))*W (norm u/U) := by rw [hs]
    _ = _ := by ring

lemma typeIMixedModel_eq (r : Eisenstein) (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) :
    typeIMixedModel r W U = ((U^(-1/6:ℝ):ℝ):ℂ)*
      angularSmoothModel r 0 (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U := by
  rw [typeIMixedModel,angularSmoothModel,←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · have hs := congrArg (fun x : ℝ => (x:ℂ)) (typeIMixed_power_scale (norm_nonneg u) hU)
    push_cast at hs
    simp only [hu,ite_true,theta,zpow_zero,one_mul]
    push_cast
    calc
      _ = (idealMoebius (r*u):ℂ)^2*(cStar:ℂ)*((norm (r*u)^(-1/6:ℝ):ℝ):ℂ)*
          (((U^(-1/6:ℝ):ℝ):ℂ)*(((norm u/U)^(-1/6:ℝ):ℝ):ℂ))*W (norm u/U) := by rw [hs]; ring
      _ = _ := by ring
  · simp only [hu,ite_false,mul_zero]

def UniformLogWeights.logarithmicWithLength {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) :
    LogarithmicWeightFamily (fun z : γ × {X : ℝ // 1 ≤ X} => (z.2:ℝ))
      (fun z x => W z.1 x) := by
  refine ⟨fun z => z.2.property,fun z => hW.compact z.1,
    fun z => hW.positive z.1,fun z => hW.smooth z.1,
    hW.radius,hW.radius_nonneg,fun z => hW.support_bound z.1,?_⟩
  intro n
  obtain ⟨C,hC,hbound⟩ := hW.derivative_bound n
  exact ⟨C,0,hC,fun z u => by simpa using hbound z.1 u⟩

end CubicFirstMoment

end

end OAI
