import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudget
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudgetSize
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelSieveAlgebra

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve Filter
open scoped BigOperators

theorem actual_kernel_image_card_eventually (c δ ε : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z J : ℕ) (P : Finset ℕ),
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      c*(Z:ℝ)/Real.log Z ≤ J → J ≤ 2*Z →
      commonCenterCutoff Z ≤ P.card →
      commonCenterMomentScale J Z (evenMomentParameter (parameterX T) Z)/4 ≤
        2*(J:ℝ)*(P.card:ℝ)^(evenMomentParameter (parameterX T) Z-1) →
      (∀p∈P,Nat.Prime p) → (∀p∈P,Odd p) → (∀p∈P,p ≤ 2*Z) →
      ∀ e : ℕ → ℤ,(∀p∈P,e p = -1 ∨ e p = 1) →
      ∀ (S : Finset ℤ) (m U : ℕ) (h : ℤ),
      0 < U → U ≤ (2*Z)^evenMomentParameter (parameterX T) Z →
      (∀x∈S,(m:ℤ)*x-h ≠ 0) → (∀x∈S,((m:ℤ)*x-h).natAbs ≤ U) →
      (∀x∈S,δ ≤ |signedJacobiAverage P e (canonicalSignedKernel ((m:ℤ)*x-h))|) →
      ((canonicalKernelImage S m h).card:ℝ) ≤ (parameterX T:ℝ)^ε := by
  obtain ⟨C,hC,hHB⟩ := heathBrown_signed_quadratic_large_sieve (ε/16) (by positivity)
  have hconst : ∀ᶠ T : ℝ in atTop,2*C ≤ (parameterX T:ℝ)^(ε/2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε/2)).comp
      ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp parameterX_tendsto)).eventually_ge_atTop (2*C)
  filter_upwards [actual_kernel_sieve_count_inputs_eventually δ hδ,
    eventually_kernelCoefficient_budget c δ (ε/4) hc hδ (by positivity),
    eventually_kernelCoefficient_cutoff_rpow 1 (by norm_num),hconst,
    parameterX_tendsto.eventually_ge_atTop 1] with T hcount hbudget hsize hconstant hX
  intro Z J P hZl hZu hJ hJu hPJ hcenter hP ho hH e he S m U h hU hUN hnz hbound hbias
  let k := evenMomentParameter (parameterX T) Z
  let N := (2*Z)^k
  let E : ℝ := (k.factorial:ℝ)/(P.card:ℝ)^k
  have hN : 0 < N := lt_of_lt_of_le hU hUN
  have hec := hcount Z P hZl hPJ hP ho (2*Z) hH e he S m U h hnz hbound hbias
  have hhb := hHB U N hU hN (kernelCoefficientInterval N) (kernelCoefficient P e k)
    (kernelCoefficientInterval_subset N)
  have henergy : coefficientEnergy (kernelCoefficientInterval N) (kernelCoefficient P e k) ≤ E := hec.1
  have hcombined : (δ^k/2)^2*((canonicalKernelImage S m h).card:ℝ) ≤
      C*((U:ℝ)*N)^(ε/16)*((U:ℝ)+N)*E :=
    hec.2.trans (hhb.trans (mul_le_mul_of_nonneg_left henergy (by positivity)))
  have hb : (N:ℝ)*E*(2/δ^k)^2 ≤ (parameterX T:ℝ)^(ε/4) := by
    simpa only [N,E,k,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] using
      hbudget Z J P.card hZl hZu hJ hJu hPJ hcenter
  have hcard := kernel_sieve_card_algebra hUN hδ hC.le (show 0 ≤ E by positivity) hcombined hb
  have hXp : (0:ℝ) < parameterX T := by exact_mod_cast (show 0 < parameterX T by omega)
  have hNs : (N:ℝ) ≤ (parameterX T:ℝ)^2 := by
    simpa only [show (1:ℝ)+1=2 by norm_num,Real.rpow_two] using hsize Z hZl hZu
  have hUs : (U:ℝ) ≤ (parameterX T:ℝ)^2 := (Nat.cast_le.mpr hUN).trans hNs
  have hprod : (U:ℝ)*N ≤ (parameterX T:ℝ)^4 := by
    have hm := mul_le_mul hUs hNs (Nat.cast_nonneg N) (by positivity : 0 ≤ (parameterX T:ℝ)^2)
    nlinarith
  have hpow : ((U:ℝ)*N)^(ε/16) ≤ (parameterX T:ℝ)^(ε/4) := by
    calc
      _ ≤ ((parameterX T:ℝ)^4)^(ε/16) := Real.rpow_le_rpow (by positivity) hprod (by positivity)
      _ = _ := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]
        congr 1
        ring
  calc
    _ ≤ 2*C*((U:ℝ)*N)^(ε/16)*(parameterX T:ℝ)^(ε/4) := hcard
    _ ≤ (parameterX T:ℝ)^(ε/2)*(parameterX T:ℝ)^(ε/4)*(parameterX T:ℝ)^(ε/4) := by gcongr
    _ = _ := by rw [←Real.rpow_add hXp,←Real.rpow_add hXp]; congr 1; ring

end Ostmann.QuadraticCenter

end

end OAI
