import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCriticalKernel

namespace OAI

/-! The complete retained frequency estimate passes through the actual
critical-line Mellin kernel with its common, integrable weight. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_actual_retained_kernel
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ c : ℝ,
      ((∫ t in T..2*T, ‖∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
        (fun u => ∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
          mellinPhase u (metaplecticDualNorm nd)) τ t‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T)))*
              (∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_retained_mean ha hε hMV hM
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
  have hmean (τ : ℝ) : (∫ t in T..2*T, ‖P (τ-t)‖)/T ≤ B*Real.sqrt (norm r) :=
    (div_le_iff₀ hR).mp (hb r hr hsr S J T hJ hT hS ℓ τ)
  have hk := metaplectic_critical_kernel_mean ℓ W hW hpos hsm c P hP hT hmean
  apply (div_le_iff₀ hR).mpr
  calc
    _ ≤ (B*Real.sqrt (norm r))*(∫ τ : ℝ, ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖) := hk
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
