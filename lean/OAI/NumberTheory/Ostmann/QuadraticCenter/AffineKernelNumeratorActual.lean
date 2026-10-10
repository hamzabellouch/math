import OAI.NumberTheory.Ostmann.QuadraticCenter.AffineKernelNumeratorBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.AffineKernelNumeratorScale
import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientParameters

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem actual_affine_kernel_inputs_eventually (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z : ℕ) (P : Finset ℕ),
      T/2 ≤ Real.log Z → commonCenterCutoff Z ≤ P.card →
      (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ P, Z ≤ p) →
      ∀ ε : ℕ → ℤ, (∀ p ∈ P, ε p = -1 ∨ ε p = 1) →
      ∀ (A B : Set ℕ) (S : Finset ℤ),
      S ⊆ positiveIntegerWindow A (parameterX T) ∪ negativeIntegerWindow B (parameterX T) →
      ∀ (m : ℕ) (h : ℤ), 0 < m → m ≤ quadraticLiftMultiplierBound Z →
      h.natAbs ≤ quadraticLiftHeight (parameterX T) Z →
      (∀ x ∈ S, c ≤ |affineKernelAverage P ε m h x|) →
      let X := parameterX T
      let k := evenMomentParameter X Z
      let U := m*X+h.natAbs
      0 < U ∧ (U : ℝ) ≤ 4*(X : ℝ)*(Z : ℝ)^(13/100 : ℝ) ∧
      U < Z^k ∧ U ≤ (2*Z)^k ∧
      (∀ x ∈ S, (m : ℤ)*x-h ≠ 0 ∧ ((m : ℤ)*x-h).natAbs ≤ U ∧
        (canonicalSignedKernel ((m : ℤ)*x-h)).natAbs ≤ U ∧
        c/2 ≤ |signedJacobiAverage P ε (canonicalSignedKernel ((m : ℤ)*x-h))|) := by
  filter_upwards [eventually_kernel_population_inputs c hc,
    eventually_nat_condition_of_logBand (eventually_ge_atTop (2 : ℕ)),
    parameterX_tendsto.eventually_ge_atTop 1] with T hpop hZtwo hX
  intro Z P hZl hPJ hP hlarge ε hε A B S hS m h hm hmcap hhcap hbias
  dsimp only
  have hZ := hZtwo Z hZl
  have hparams := hpop Z P.card hZl hPJ
  have hU := affine_numerator_range_lt_power hX hZ hmcap hhcap
  refine ⟨by positivity,
    affine_numerator_range_scale hX (by omega) hmcap hhcap,
    hU, affine_numerator_range_le_coefficient_scale hX hZ hmcap hhcap, ?_⟩
  intro x hx
  have hb : c ≤ |signedJacobiAverage P ε ((m : ℤ)*x-h)| := hbias x hx
  have hnz := numerator_ne_zero_of_signed_average hP ε hc hb
  have hnum := affine_numerator_natAbs_le (m := m) (h := h) (hS hx)
  have hpow : ((m : ℤ)*x-h).natAbs < Z^(evenMomentParameter (parameterX T) Z+1) :=
    (hnum.trans_lt hU).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hk := signedJacobiAverage_kernel_lower hP ε hε
    (kernelFactorization ((m : ℤ)*x-h) hnz) (by omega : 1 ≤ Z) hlarge hpow hb
    hparams.2.2.2.2.1
  refine ⟨hnz, hnum, (canonicalSignedKernel_abs_le _).trans hnum, ?_⟩
  simpa only [canonicalSignedKernel, dite_eq_right hnz] using hk

end Ostmann.QuadraticCenter

end

end OAI
