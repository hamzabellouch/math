import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IndexedWitnessFilling
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SumEquiv

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving
open OrdinaryCorrelations.SharedSlotPatterns OrdinaryCorrelations.SourceCylinder
open Finset Classical Filter

noncomputable def sourceWitnessDelta (C₀ : ℝ) (h : ℕ) (B : ℝ) : ℝ :=
  max (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B) /
    (sourceMinPrime B * Real.log 2)) ((2+B)/sourceMinPrime B)

noncomputable def sourceWitnessPrefactor (C₀ B : ℝ) : ℝ :=
  let ℓ := sourceLength B
  let L := pathLength B
  let t := listCutoff B
  let J := ⌈C₀*Real.log B⌉₊
  let N := witnessSlotCount ℓ L J t
  cylinderBudget (sourceListSlotBudget C₀ B) *
    (A^(ℓ*J)*2^N) * (witnessTemplateBudget ℓ L J t:ℝ) *
      (max 1 (∑ p ∈ (sourceSystem B).primes, (p:ℝ)⁻¹))^N

lemma sourceWitnessPrefactor_nonneg (C₀ B : ℝ) : 0 ≤ sourceWitnessPrefactor C₀ B := by
  unfold sourceWitnessPrefactor
  exact mul_nonneg (mul_nonneg (mul_nonneg (cylinderBudget_nonneg _)
    (mul_nonneg (pow_nonneg A_pos.le _) (by positivity))) (Nat.cast_nonneg _))
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

theorem source_witness_majorant_envelope (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ) (hτ : τ < 2) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀),
      sourceWitnessDelta C₀ h B ≤ 1 →
      NumericalLine.sourceWitnessMajorant D h ≤
        sourceWitnessPrefactor C₀ B * (sourceWitnessDelta C₀ h B)^⌈B^(2*epsilon)⌉₊ := by
  filter_upwards [source_configuration_certificate h hh τ C₀ hτ,
    eventually_ge_atTop (1:ℝ)] with B hc hB
  intro D hδ
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hK := PrivateFamily.testSize_nonneg B C₀ h (sourceLength B) (pathLength B)
  have hm := configurationMass_le_templateMass (D:=D) (h:=h)
    (ℓ:=sourceLength B) (L:=pathLength B) (t:=listCutoff B)
    (sourceMinPrime B) (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B))
    ⌈B^(2*epsilon)⌉₊ (fun x => Classical.choice (hc D x.val x.property))
  have ht := witnessTemplateMass_le (sourceSystem B) (sourceMinPrime B) B
    (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B)) h
    (sourceLength B) (pathLength B) ⌈C₀*Real.log B⌉₊ (listCutoff B) ⌈B^(2*epsilon)⌉₊
    hP (zero_le_one.trans hB) hK
    (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩) hδ
  unfold NumericalLine.sourceWitnessMajorant
  rw [WitnessConfiguration.sum_crude_eq]
  apply (mul_le_mul_of_nonneg_left WitnessConfiguration.sum_crude_le (cylinderBudget_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hm.trans ht)
    (mul_nonneg (pow_nonneg A_pos.le _) (by positivity))) (cylinderBudget_nonneg _)).trans_eq
  unfold sourceWitnessPrefactor sourceWitnessDelta
  ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
