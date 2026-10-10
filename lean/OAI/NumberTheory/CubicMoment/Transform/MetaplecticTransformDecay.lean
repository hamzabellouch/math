import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTransformContour

namespace OAI

/-! The exact far-left height bound for the shifted metaplectic transform.
The power of the height is 4m, proved by finite Gamma recurrence. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticShiftTransform (ℓ : ℤ) (W : ℝ → ℂ) (b v t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    (v:ℂ)^((b:ℂ)+(τ:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((b:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W ((b:ℂ)+(τ:ℂ)*Complex.I)

lemma metaplecticShiftTransform_zero (ℓ : ℤ) (W : ℝ → ℂ) (σ v : ℝ) :
    metaplecticShiftTransform ℓ W (-σ) v 0 = metaplecticTransform ℓ W σ v := by
  simp only [metaplecticShiftTransform,metaplecticTransform,sub_zero]

/-- Uniform in the scale and height; the constant depends only on the
fixed angular mode, weight and chosen far-left line. -/
theorem metaplecticShiftTransform_far_left (ℓ : ℤ) (m : ℕ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticShiftTransform ℓ W (1/2-(m:ℝ)) v t‖ ≤
        C*v^(1/2-(m:ℝ))*(1+|t|)^(4*m) := by
  obtain ⟨Cg,hCg,hQ⟩ := metaplecticGamma_half_integer_bound ℓ m
  obtain ⟨Cw,hCw,hdecay⟩ := mellin_polynomial_majorant W hW hpos hsm
    (1/2-(m:ℝ)) (4*m)
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hI : 0 ≤ I := integral_nonneg (fun τ => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*Cg*Cw*I,by positivity,?_⟩
  intro v hv t
  have hb (τ : ℝ) :
      ‖(v:ℂ)^(((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((1/2-(m:ℝ):ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
        mellin W (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ ≤
      (v^(1/2-(m:ℝ))*Cg*Cw*(1+|t|)^(4*m))*mellinEdgeMajorant 1 τ := by
    have he : (((1/2-(m:ℝ):ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
        (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hq := hQ (τ-t)
    rw [←he] at hq
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I).re = 1/2-(m:ℝ) := by simp
    rw [hre]
    calc
      _ ≤ (v^(1/2-(m:ℝ))*(Cg*(1+|τ-t|)^(4*m)))*
          ‖mellin W (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ := by
        gcongr
      _ = (v^(1/2-(m:ℝ))*Cg)*
          (‖mellin W (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(4*m)) := by ring
      _ ≤ (v^(1/2-(m:ℝ))*Cg)*mellinEdgeMajorant (Cw*(1+|t|)^(4*m)) τ :=
        mul_le_mul_of_nonneg_left (hdecay t τ) (by positivity)
      _ = _ := by unfold mellinEdgeMajorant; ring
  rw [metaplecticShiftTransform,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)‖*
        (∫ τ : ℝ, (v^(1/2-(m:ℝ))*Cg*Cw*(1+|t|)^(4*m))*mellinEdgeMajorant 1 τ) := by
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      exact norm_integral_le_of_norm_le ((mellinEdgeMajorant_integrable 1).const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]; dsimp [I]; ring

end CubicFirstMoment

end

end OAI
