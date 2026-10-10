import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrefixBound
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrefixCutoff

namespace OAI

/-! The complete coded norm-block mean. All supported prefixes are summed,
using only the actual coefficient bound and Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_supported_block_mean {ε M : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : Eisenstein → MetaplecticDualArgument → ℂ)
      (C : ℝ), 0 ≤ C → ∀ r : Eisenstein, primary r →
      ∀ S : Finset (MetaplecticRetainedCode r),
      (∀ z ∈ S, IsCoprime z.2.2.val r) →
      (∀ z ∈ S, ∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) →
      (∀ z ∈ S, ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) →
      ∀ I T : ℝ, 0 < I → 0 < T →
      (∀ z ∈ S, I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) →
      ∀ ℓ : ℤ, ∀ τ : ℝ,
      ((∫ t in T..2*T, ‖∑ z ∈ S,
        metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
          mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z))‖)/T)/
        Real.sqrt (norm r) ≤
          D*C*(3*I)^(3*ε/2)*norm r^(2*ε)*(1+Real.sqrt (2*I/(norm r*T))) := by
  obtain ⟨B,hB,hmean⟩ := metaplectic_code_mean hε hMV hM
  obtain ⟨E,hE,hsum⟩ := metaplectic_prefix_amplitude_sum hε
  let A := Real.sqrt (M*B)+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A*E,mul_pos hA hE,?_⟩
  intro a C hC r hr S hcop hsupport hcoef I T hI hT hdyad ℓ τ
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRroot := Real.sqrt_pos.mpr hR
  have hJ : 0 < 3*I := by positivity
  let P := S.image metaplecticCodePrefix
  let q := fun p : MetaplecticDyadPrefix r => metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
    (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T))
  have hq (p : MetaplecticDyadPrefix r) : 0 ≤ q p := by
    dsimp [q]
    exact mul_nonneg (div_nonneg (metaplecticPrefixAmplitude_nonneg hr hC p) hRroot.le)
      (by positivity)
  have hjp (p : MetaplecticDyadPrefix r) :
      (I/metaplecticFreeScale p)^(ε/2) ≤ (3*I)^(ε/2) :=
    Real.rpow_le_rpow (div_nonneg hI.le (metaplecticFreeScale_pos p).le)
      (metaplectic_free_length_upper p hI.le) (by positivity)
  have hc := hmean a C hC r hr S hcop hcoef I T hT hdyad ℓ τ
  have hs := hsum r hr P (3*I) hJ (metaplectic_prefix_support S hsupport)
    (metaplectic_prefix_cutoff S (fun z hz => (hdyad z hz).2)) C hC I T
  calc
    _ ≤ (∑ p ∈ P, Real.sqrt (M*B)*(I/metaplecticFreeScale p)^(ε/2)*
        metaplecticPrefixAmplitude r C p*(1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)))/
          Real.sqrt (norm r) := div_le_div_of_nonneg_right hc hRroot.le
    _ = ∑ p ∈ P, Real.sqrt (M*B)*(I/metaplecticFreeScale p)^(ε/2)*q p := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [q]
      ring
    _ ≤ ∑ p ∈ P, A*(3*I)^(ε/2)*q p := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (hq p)
      exact mul_le_mul (by dsimp [A]; linarith [Real.sqrt_nonneg (M*B)]) (hjp p)
        (Real.rpow_nonneg (div_nonneg hI.le (metaplecticFreeScale_pos p).le) _) hA.le
    _ = A*(3*I)^(ε/2)*(∑ p ∈ P, q p) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(3*I)^(ε/2)*(E*C*(3*I)^ε*norm r^(2*ε)*
        (1+Real.sqrt (2*I/(norm r*T)))) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [show 3*ε/2 = ε/2+ε by ring,Real.rpow_add hJ]
      ring

end CubicFirstMoment

end

end OAI
