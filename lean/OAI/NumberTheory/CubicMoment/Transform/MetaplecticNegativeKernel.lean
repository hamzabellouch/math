import OAI.NumberTheory.CubicMoment.Transform.MetaplecticConjugateMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCriticalKernel

namespace OAI

/-! The same actual critical kernel on the negative height dyad.
Conjugating the coefficients supplies the required opposite-sign mean. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_negative_kernel_mean (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) (P : ℝ → ℂ) (hP : Continuous P)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ τ : ℝ, (∫ t in T..2*T, ‖P (τ+t)‖)/T ≤ B) :
    (∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c P τ (-t)‖)/T ≤
      B*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  have hm := (metaplectic_mellin_half_integrable W hW hpos hsm).norm
  have hc : Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 (-z.2)) :=
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP).comp
      (f := fun z : ℝ × ℝ => (z.1,-z.2)) (continuous_fst.prodMk continuous_snd.neg)
  have hb (τ : ℝ) :
      (∫ t in T..2*T, ‖metaplecticCriticalKernel ℓ W c P τ (-t)‖) ≤
        (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖ := by
    simp only [norm_metaplecticCriticalKernel,sub_neg_eq_add]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*(B*T) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).mp (hmean τ)) (_root_.norm_nonneg _)
      _ = _ := by ring
  have hi := integral_height_norm_le
    (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 (-z.2)) hc
    (show T ≤ 2*T by linarith)
    (fun τ => (B*T)*‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) (hm.const_mul (B*T)) hb
  rw [integral_const_mul] at hi
  apply (div_le_iff₀ hT).mpr
  nlinarith only [hi]

theorem metaplectic_actual_retained_negative_kernel
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ c : ℝ,
      ((∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
        (fun u => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
          mellinPhase u (metaplecticDualNorm nd)) τ (-t)‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_retained_plus_mean ha hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ W hW hpos hsm c
  have hR := Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))
  let B := ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
    (1+Real.sqrt (4*J/(norm r*T)))
  let P := fun u : ℝ => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
    mellinPhase u (metaplecticDualNorm nd)
  have hP : Continuous P := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hmean (τ : ℝ) : (∫ t in T..2*T, ‖P (τ+t)‖)/T ≤ B*Real.sqrt (norm r) :=
    (div_le_iff₀ hR).mp (hb r hr hsr S J T hJ hT hS ℓ τ)
  have hk := metaplectic_negative_kernel_mean ℓ W hW hpos hsm c P hP hT hmean
  apply (div_le_iff₀ hR).mpr
  calc
    _ ≤ (B*Real.sqrt (norm r))*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := hk
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
