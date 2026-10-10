import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedTransform
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedLow
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth

namespace OAI

/-! Polynomial height growth of the actual twisted Voronoi remainder.
Only the original Voronoi input is used; Gamma growth is already proved. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticTransform_twisted_polynomial (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ : ℝ} (hσ : 0 < σ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ v : ℝ, 0 < v → ∀ t : ℝ,
      ‖metaplecticTransform ℓ (fun x => W x*mellinPhase t x) σ v‖ ≤
        C*v^(-σ)*(1+|t|)^N := by
  obtain ⟨Cg,N,hCg,hQ⟩ := metaplecticGamma_strip_bound ℓ (-σ)
    (angularGammaQuotientStripBound_proved _ _ (by
      linarith [metaplecticAngularShift_nonneg ℓ]))
    (angularGammaQuotientStripBound_proved _ _ (by
      linarith [metaplecticAngularShift_nonneg ℓ]))
  obtain ⟨Cw,hCw,hdecay⟩ := mellin_polynomial_majorant W hW hpos hsm (-σ) N
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hI : 0 ≤ I := integral_nonneg (fun τ => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*Cg*Cw*I,N,by positivity,?_⟩
  intro v hv t
  rw [metaplecticTransform_twisted ℓ W σ hv t,norm_mul,mellinPhase_norm,one_mul]
  have hb (τ : ℝ) :
      ‖(v:ℂ)^(((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
        mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ ≤
      (v^(-σ)*Cg*Cw*(1+|t|)^N)*mellinEdgeMajorant 1 τ := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I).re = -σ := by simp
    rw [hre]
    calc
      _ ≤ (v^(-σ)*(Cg*(1+|τ-t|)^N))*
          ‖mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)‖ := by
        gcongr
        exact hQ (-σ) ⟨le_rfl,by linarith⟩ (τ-t)
      _ = (v^(-σ)*Cg)*
          (‖mellin W (((-σ:ℝ):ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^N) := by ring
      _ ≤ (v^(-σ)*Cg)*mellinEdgeMajorant (Cw*(1+|t|)^N) τ :=
        mul_le_mul_of_nonneg_left (hdecay t τ) (by positivity)
      _ = _ := by unfold mellinEdgeMajorant; ring
  rw [metaplecticShiftTransform,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)‖*
        (∫ τ : ℝ, (v^(-σ)*Cg*Cw*(1+|t|)^N)*mellinEdgeMajorant 1 τ) := by
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      exact norm_integral_le_of_norm_le ((mellinEdgeMajorant_integrable 1).const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]; dsimp [I]; ring

theorem metaplecticCompleted_twisted_polynomial
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ : ℝ} (hσ : 0 < σ) (hσs : σ < 1/10000) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ t : ℝ,
      ‖metaplecticCompleted r 0 (fun x => W x*mellinPhase t x) X-
        metaplecticMain r 0 (fun x => W x*mellinPhase t x) X‖ ≤
        C*X^(-σ)*(1+|t|)^N := by
  obtain ⟨C,N,hC,hTr⟩ := metaplecticTransform_twisted_polynomial 0 W hW hpos hsm hσ
  obtain ⟨M,hM,hMass⟩ := metaplectic_coefficient_mass_small_power hV.1
    (show (0:ℝ) < 1 by norm_num) hσ
  let S : ℝ := ∑' d : PrimaryArgument, norm d^(-5/2-3*σ)
  have hS : 0 ≤ S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let D : ℝ := ‖metaplecticPrefactor r 0‖*C*(2*Real.pi)^(-4*σ)*
    norm r^(2*σ)*(M*norm r)*S
  have hR := norm_nonneg r
  refine ⟨D,N,by dsimp [D]; positivity,?_⟩
  intro X hX t
  have ht : 0 ≤ C*(1+|t|)^N := by positivity
  have htransform (v : ℝ) (hv : 0 < v) :
      ‖metaplecticTransform 0 (fun x => W x*mellinPhase t x) σ v‖ ≤
        (C*(1+|t|)^N)*v^(-σ) := by
    simpa only [mul_right_comm] using hTr v hv t
  have hbound := metaplecticDualTerm_tsum_norm_bound hr 0
    (fun x => W x*mellinPhase t x) hσ hX ht htransform
    (hMass r hr hsr).1 (hMass r hr hsr).2
  rw [metaplectic_angular_voronoi hV hr hsr 0 _ (phaseWeight_compact hW t)
    (phaseWeight_positive hpos t) (phaseWeight_smooth hpos hsm t) hX hσ hσs,
    add_sub_cancel_left,norm_mul]
  calc
    _ ≤ ‖metaplecticPrefactor r 0‖*
        ((C*(1+|t|)^N)*((2*Real.pi)^(-4*σ)*X^(-σ)*norm r^(2*σ)))*
        (M*norm r^(1:ℝ))*S := by
      simpa only [mul_assoc,S] using
        mul_le_mul_of_nonneg_left hbound (_root_.norm_nonneg (metaplecticPrefactor r 0))
    _ = _ := by dsimp [D]; rw [Real.rpow_one]; ring

end CubicFirstMoment

end

end OAI
