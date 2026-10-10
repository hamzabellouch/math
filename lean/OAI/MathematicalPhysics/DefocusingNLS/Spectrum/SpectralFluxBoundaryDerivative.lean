import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobin
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! The parameter derivative of the weighted Robin boundary operator. -/

namespace DefocusingNLS

noncomputable def spectralFluxBoundarySlope (R μ : ℝ)
    (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ((R : ℂ)^11) • ((μ : ℂ) • M')

theorem spectralFluxBoundary_hasDerivAt (R μ A : ℝ)
    (M : ℂ → (ℂ × ℂ →L[ℂ] ℂ × ℂ)) (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ)
    (hM : HasDerivAt M M' z) :
    HasDerivAt (fun t => spectralFluxBoundary R μ A (M t)) (spectralFluxBoundarySlope R μ M') z := by
  exact ((hM.const_smul (μ : ℂ)).sub_const ((A : ℂ) • spectralPairSkew ℂ)).const_smul ((R : ℂ)^11)

theorem spectralFluxBoundary_chain_condition (R μ A : ℝ) (hR : R ≠ 0) (hμ : μ ≠ 0)
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x₀ x₁ dx₁ : ℂ × ℂ) :
    ((R : ℂ)^11*((μ : ℂ)*dx₁.1-(A : ℂ)*x₁.2),
      (R : ℂ)^11*((μ : ℂ)*dx₁.2+(A : ℂ)*x₁.1)) =
      spectralFluxBoundary R μ A M x₁ + spectralFluxBoundarySlope R μ M' x₀ ↔
    dx₁ = M x₁ + M' x₀ := by
  rw [spectralFluxBoundary_apply]
  have hr : (R : ℂ)^11 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hR)
  have hm : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hS : spectralFluxBoundarySlope R μ M' x₀ =
      ((R : ℂ)^11*((μ : ℂ)*(M' x₀).1), (R : ℂ)^11*((μ : ℂ)*(M' x₀).2)) := by
    rfl
  rw [hS]
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change _ = _ + _ at h₁ h₂
    apply Prod.ext
    · apply mul_left_cancel₀ hm
      apply mul_left_cancel₀ hr
      change _ = (R : ℂ)^11 * ((μ : ℂ)*((M x₁).1+(M' x₀).1))
      linear_combination h₁
    · apply mul_left_cancel₀ hm
      apply mul_left_cancel₀ hr
      change _ = (R : ℂ)^11 * ((μ : ℂ)*((M x₁).2+(M' x₀).2))
      linear_combination h₂
  · intro h
    rw [h]
    apply Prod.ext <;> change _ = _ + _ <;> dsimp only [Prod.fst_add,Prod.snd_add] <;> ring

end DefocusingNLS

end OAI
