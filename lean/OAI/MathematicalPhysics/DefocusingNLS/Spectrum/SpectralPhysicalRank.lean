import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralColumnRank

namespace OAI

/-! The exact physical coordinate change preserves the rank of the two slow columns. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralPhysicalState (νp νm : ℂ) (r : ℝ) (z : E₄) : E₄ :=
  ((Complex.exp (νp*(Real.log r : ℂ))*z.1.1,
      Complex.exp (νp*(Real.log r : ℂ))/(r : ℂ)*(νp*z.1.1+z.1.2)),
   (Complex.exp (νm*(Real.log r : ℂ))*z.2.1,
      Complex.exp (νm*(Real.log r : ℂ))/(r : ℂ)*(νm*z.2.1+z.2.2)))

noncomputable def spectralPhysicalStateLinear (νp νm : ℂ) (r : ℝ) : E₄ →ₗ[ℂ] E₄ where
  toFun := spectralPhysicalState νp νm r
  map_add' := by
    intro v w
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [spectralPhysicalState,Prod.fst_add,Prod.snd_add]
    all_goals ring
  map_smul' := by
    intro a v
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [spectralPhysicalState,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply]
    all_goals ring

theorem spectralPhysicalState_injective (νp νm : ℂ) (r : ℝ) (hr : r ≠ 0) :
    Function.Injective (spectralPhysicalStateLinear νp νm r) := by
  intro v w he
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hp := Complex.exp_ne_zero (νp*(Real.log r : ℂ))
  have hm := Complex.exp_ne_zero (νm*(Real.log r : ℂ))
  have h11 := congrArg (fun z : E₄ => z.1.1) he
  have h12 := congrArg (fun z : E₄ => z.1.2) he
  have h21 := congrArg (fun z : E₄ => z.2.1) he
  have h22 := congrArg (fun z : E₄ => z.2.2) he
  change Complex.exp (νp*(Real.log r : ℂ))*v.1.1=
    Complex.exp (νp*(Real.log r : ℂ))*w.1.1 at h11
  change Complex.exp (νm*(Real.log r : ℂ))*v.2.1=
    Complex.exp (νm*(Real.log r : ℂ))*w.2.1 at h21
  have hv11 := mul_left_cancel₀ hp h11
  have hv21 := mul_left_cancel₀ hm h21
  change Complex.exp (νp*(Real.log r : ℂ))/(r : ℂ)*(νp*v.1.1+v.1.2)=
    Complex.exp (νp*(Real.log r : ℂ))/(r : ℂ)*(νp*w.1.1+w.1.2) at h12
  change Complex.exp (νm*(Real.log r : ℂ))/(r : ℂ)*(νm*v.2.1+v.2.2)=
    Complex.exp (νm*(Real.log r : ℂ))/(r : ℂ)*(νm*w.2.1+w.2.2) at h22
  have hv12 := mul_left_cancel₀ (div_ne_zero hp hrC) h12
  have hv22 := mul_left_cancel₀ (div_ne_zero hm hrC) h22
  rw [hv11] at hv12
  rw [hv21] at hv22
  exact Prod.ext (Prod.ext hv11 (add_left_cancel hv12))
    (Prod.ext hv21 (add_left_cancel hv22))

theorem spectralPhysicalPair_rank (νp νm : ℂ) (Yp Ym : ℝ → E₄)
    (r : ℝ) (hr : r ≠ 0)
    (hY : LinearIndependent ℂ ![Yp (Real.log r),Ym (Real.log r)]) :
    LinearIndependent ℂ ![spectralPhysicalPair νp νm Yp r,
      spectralPhysicalPair νp νm Ym r] := by
  have h := hY.map' (spectralPhysicalStateLinear νp νm r)
    (LinearMap.ker_eq_bot.mpr (spectralPhysicalState_injective νp νm r hr))
  have he : spectralPhysicalStateLinear νp νm r ∘ ![Yp (Real.log r),Ym (Real.log r)]=
      ![spectralPhysicalPair νp νm Yp r,spectralPhysicalPair νp νm Ym r] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

end DefocusingNLS

end OAI
