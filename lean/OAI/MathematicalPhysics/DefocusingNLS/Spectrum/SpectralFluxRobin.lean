import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderOperator

namespace OAI

/-! The boundary operator of the weak flux equation is the weighted Robin operator. -/

namespace DefocusingNLS

noncomputable def spectralFluxBoundary (R μ A : ℝ)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ((R : ℂ)^11) • ((μ : ℂ) • M-(A : ℂ) • spectralPairSkew ℂ)

theorem spectralFluxBoundary_apply (R μ A : ℝ)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x : ℂ × ℂ) :
    spectralFluxBoundary R μ A M x=
      ((R : ℂ)^11*((μ : ℂ)*(M x).1-(A : ℂ)*x.2),
       (R : ℂ)^11*((μ : ℂ)*(M x).2+(A : ℂ)*x.1)) := by
  apply Prod.ext <;>
    simp [spectralFluxBoundary,spectralPairSkew,smul_eq_mul]

theorem spectralFluxBoundary_condition (R μ A : ℝ) (hR : R ≠ 0) (hμ : μ ≠ 0)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x dx : ℂ × ℂ) :
    ((R : ℂ)^11*((μ : ℂ)*dx.1-(A : ℂ)*x.2),
     (R : ℂ)^11*((μ : ℂ)*dx.2+(A : ℂ)*x.1))=spectralFluxBoundary R μ A M x ↔ dx=M x := by
  rw [spectralFluxBoundary_apply]
  have hr : (R : ℂ)^11 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hR)
  have hm : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  constructor
  · intro h
    have h₁ := mul_left_cancel₀ hr (congrArg Prod.fst h)
    have h₂ := mul_left_cancel₀ hr (congrArg Prod.snd h)
    apply Prod.ext
    · exact mul_left_cancel₀ hm (sub_left_inj.mp h₁)
    · exact mul_left_cancel₀ hm (add_right_cancel h₂)
  · rintro rfl
    rfl

theorem spectralGaugeFluxBoundary_condition (R μ A : ℝ) (hR : R ≠ 0) (hμ : μ ≠ 0)
    (q dq : ℂ) (hq : q ≠ 0) (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x dx : ℂ × ℂ) :
    ((R : ℂ)^11*((μ : ℂ)*dx.1-(A : ℂ)*x.2),
     (R : ℂ)^11*((μ : ℂ)*dx.2+(A : ℂ)*x.1))=
      spectralFluxBoundary R μ A (spectralGaugeRobin q dq M) x ↔
    spectralGaugeColumns q dx+spectralGaugeColumns dq x=M (spectralGaugeColumns q x) := by
  rw [spectralFluxBoundary_condition R μ A hR hμ]
  exact (spectralGaugeRobin_condition q dq hq M x dx).symm

end DefocusingNLS

end OAI
