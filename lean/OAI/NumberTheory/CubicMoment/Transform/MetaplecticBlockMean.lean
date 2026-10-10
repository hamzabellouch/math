import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBlockCoefficient
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualTailWeights

namespace OAI

/-! Mean value of an actual retained free-variable block, with all
coefficient amplitudes supplied by the literal Voronoi coefficient bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_block_frequency (d : PrimaryArgument) (n : MetaplecticDualArgument)
    (j : ℤ) (hj : -1 ≤ j) (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3) :
    metaplecticDualNorm (n,d) =
      (norm d^3*((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3))*norm w := by
  unfold metaplecticDualNorm
  rw [metaplectic_frequency_norm n (j+1).toNat ζ h h' w
    (metaplectic_numerator_of_frequency n hj ζ h h' w he)]
  ring

/-- The finite subset can include arbitrary further restrictions. In
particular this applies to each actual norm dyad of the retained sum. -/
theorem metaplectic_actual_block_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ (d : PrimaryArgument) (ℓ j : ℤ), -1 ≤ j → ∀ (ζ : Eisensteinˣ)
      (h h' : Eisenstein), primary h → primary h' →
      ∀ (S : Finset Eisenstein) (n : Eisenstein → MetaplecticDualArgument),
      (∀ w ∈ S, primary w) → (∀ w ∈ S, IsCoprime w r) →
      (∀ w ∈ S, metaplecticFrequency (n w) =
        traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3) →
      (∀ w ∈ S, ‖a r (n w)‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) →
      ∀ L T u : ℝ, 1 ≤ L → 0 < T →
      (∀ w ∈ S, L/2 ≤ norm w ∧ norm w ≤ L) →
      (∫ t in T..2*T, ‖∑ w ∈ S,
        metaplecticNormalizedDualCoefficient a r ℓ (n w,d)*
          mellinPhase (t+u) (metaplecticDualNorm (n w,d))‖)/T ≤
        Real.sqrt (M*D)*L^(ε/2)*
          (C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*
            min (norm r) (norm h*norm h') /
            (Real.sqrt ((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)*norm d))*
          (1+Real.sqrt (2*L/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_scaled_free_meanAbsolute hε hMV hM
  refine ⟨D,hD,?_⟩
  intro a C hC r hr d ℓ j hj ζ h h' hh hh' S n hS hwr he ha L T u hL hT hsize
  let v : Eisenstein → ℂ := fun w => metaplecticNormalizedDualCoefficient a r ℓ (n w,d)
  let c : ℝ := norm d^3*((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)
  let K : ℝ := C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*
    min (norm r) (norm h*norm h') /
      (Real.sqrt ((3:ℝ)^((j+1).toNat-1:ℝ)*norm h*norm h'^3)*norm d)
  have hc : 0 < c := by
    have hd := norm_pos_of_ne_zero (primary_ne_zero d.property)
    have hh0 := norm_pos_of_ne_zero (primary_ne_zero hh)
    have hp0 := norm_pos_of_ne_zero (primary_ne_zero hh')
    dsimp [c]
    positivity
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hd := norm_pos_of_ne_zero (primary_ne_zero d.property)
  have hh0 := norm_pos_of_ne_zero (primary_ne_zero hh)
  have hp0 := norm_pos_of_ne_zero (primary_ne_zero hh')
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hv (w : Eisenstein) (hw : w ∈ S) : ‖v w‖^2 ≤ K^2/norm w :=
    metaplectic_actual_free_coefficient_sq hC hr d ℓ (n w) hj ζ hh hh' (hS w hw)
      (hwr w hw) (he w hw) (ha w hw)
  have hq (w : Eisenstein) (hw : w ∈ S) : metaplecticDualNorm (n w,d) = c*norm w :=
    metaplectic_block_frequency d (n w) j hj ζ h h' w (he w hw)
  have hp := hbound S hS v L K T u c 0 hL hK hT hc hsize hv
  simp only [theta_zero,mul_one] at hp
  convert hp using 1
  congr 2
  funext t
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  rw [hq w hw]

end CubicFirstMoment

end

end OAI
