import OAI.NumberTheory.CubicMoment.Transform.MetaplecticNegativeKernel
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedEstimate

namespace OAI

/-! The actual negative-height retained Voronoi contribution, with
its unchanged exact prefactor normalization. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_retained_negative_voronoi_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ A X J T : ℝ, 0 ≤ A → 0 < X → 0 < J → 0 < T →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A) →
      (∫ t in T..2*T, ‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,
          metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase (-t) x) A X nd‖)/T ≤
        Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi))*
          (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_actual_retained_negative_kernel ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr ℓ W hW hpos hsm A X J T hA hX hJ hT hm hp
  let c := (2*Real.pi)^4*X/norm r^2
  let K := fun t : ℝ => ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
    (fun u => ∑ nd ∈ metaplecticDualBall J,
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)) τ (-t)
  let Q := ‖metaplecticPrefactor r ℓ‖*Real.sqrt c*(1/(2*Real.pi))
  let B := (((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
    (1+Real.sqrt (4*J/(norm r*T)))*
      (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖))
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb : ((∫ t in T..2*T, ‖K t‖)/T)/Real.sqrt (norm r) ≤ B :=
    hbound r hr hsr (metaplecticDualBall J) J T hJ hT
      (fun nd hnd => (mem_metaplecticDualBall nd J).mp hnd) ℓ W hW hpos hsm c
  have he (t : ℝ) : ‖metaplecticPrefactor r ℓ*
      ∑ nd ∈ metaplecticDualBall J,
        metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase (-t) x) A X nd‖ = Q*‖K t‖ := by
    rw [metaplectic_retained_critical a hr ℓ W hW hpos hsm hA hX J (-t) hm hp]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0:ℝ) ≤ 1/(2*Real.pi) by positivity)]
    dsimp [Q,K,c]
    ring
  calc
    _ = Q*((∫ t in T..2*T, ‖K t‖)/T) := by
      simp_rw [he]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ Q*(B*Real.sqrt (norm r)) :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ (Real.sqrt_pos.mpr hR)).mp hb) hQ
    _ = _ := by
      rw [show Q*(B*Real.sqrt (norm r)) = (Q*Real.sqrt (norm r))*B by ring,
        show Q*Real.sqrt (norm r) = Real.sqrt X/(3^(7/2:ℝ)*(2*Real.pi)) from
          metaplectic_critical_prefactor hr ℓ hX]

end CubicFirstMoment

end

end OAI
