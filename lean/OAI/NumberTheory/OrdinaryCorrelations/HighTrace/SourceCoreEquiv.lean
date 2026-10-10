import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ChargeKappaPos

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter

def sourceCoreEquiv (B : ℝ) : (sourceSystem B).CoreIndex ≃ ↥(SourcePrimeBands.corePrimes B) where
  toFun p := ⟨p.val.val,p.property⟩
  invFun p := ⟨⟨p.val,mem_union_left _ p.property⟩,p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma source_harmonicCore (B : ℝ) : (sourceSystem B).harmonicCore = SourcePrimeBands.coreMass B := by
  rw [harmonicCore,SourcePrimeBands.coreMass]
  rw [← sum_coe_sort (SourcePrimeBands.corePrimes B) (fun p : ℕ => (p : ℝ)⁻¹)]
  exact (sourceCoreEquiv B).sum_comp (fun p => (p.val : ℝ)⁻¹)

lemma source_bands_disjoint (B : ℝ) :
    Disjoint (SourcePrimeBands.corePrimes B) (SourcePrimeBands.centerPrimes B) := by
  apply disjoint_left.mpr
  intro p hpC hpZ
  have hC := (mem_filter.mp hpC).2.2
  have hZ := mem_filter.mp hpZ
  have hp : 0 < (p : ℝ) := by exact_mod_cast hZ.2.1.pos
  have hu : (p : ℝ) ≤ Real.exp (B^(1-SourcePrimeBands.eta)) :=
    (show (p : ℝ) ≤ (⌊Real.exp (B^(1-SourcePrimeBands.eta))⌋₊ : ℝ) by
      exact_mod_cast (mem_Icc.mp hZ.1).2).trans (Nat.floor_le (Real.exp_pos _).le)
  have hlog := Real.log_le_log hp hu
  rw [Real.log_exp] at hlog
  exact (not_lt_of_ge hlog) hC

def sourceCenterEquiv (B : ℝ) : (sourceSystem B).CenterIndex ≃ ↥(SourcePrimeBands.centerPrimes B) where
  toFun p := ⟨p.val.val,(mem_union.mp p.val.property).resolve_left p.property⟩
  invFun p := ⟨⟨p.val,mem_union_right _ p.property⟩,
    fun hc => disjoint_left.mp (source_bands_disjoint B) hc p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma source_harmonicCenter (B : ℝ) : (sourceSystem B).harmonicCenter = SourcePrimeBands.centerMass B := by
  rw [harmonicCenter,SourcePrimeBands.centerMass]
  rw [← sum_coe_sort (SourcePrimeBands.centerPrimes B) (fun p : ℕ => (p : ℝ)⁻¹)]
  exact (sourceCenterEquiv B).sum_comp (fun p => (p.val : ℝ)⁻¹)

lemma source_charge_harmonic (T : ℝ) :
    ∀ᶠ B : ℝ in atTop,
      100*Real.log B < kappa*((sourceSystem B).harmonicCore -
        T*Real.sqrt (sourceSystem B).harmonicCore) ∧
      100*Real.log B < kappa*((sourceSystem B).harmonicCore -
        T*Real.sqrt (sourceSystem B).harmonicCore) -
          (sourceSystem B).harmonicCore * betaC * (Real.exp kappa - 1) := by
  simpa only [source_harmonicCore] using source_charge_lower T

lemma source_core_eventually_one : ∀ᶠ B : ℝ in atTop, 1 ≤ (sourceSystem B).harmonicCore := by
  simpa only [source_harmonicCore] using coreMass_tendsto.eventually (eventually_ge_atTop (1 : ℝ))

theorem center_saving_coefficients :
    ∀ᶠ B : ℝ in atTop,
      epsilon/10 * Real.log B ≤ theta/2 * (sourceSystem B).harmonicCenter ∧
      theta * (sourceSystem B).harmonicCenter ≤ epsilon * Real.log B := by
  have h := SourcePrimeBands.source_prime_bands.2
  have h1 := h.const_mul (theta/2)
  have h2 := h.const_mul theta
  have hlt : epsilon/10 < theta/2 * (SourcePrimeBands.epsilon-SourcePrimeBands.eta) := by
    norm_num [epsilon,SourcePrimeBands.epsilon,SourcePrimeBands.eta]
  have hgt : theta * (SourcePrimeBands.epsilon-SourcePrimeBands.eta) < epsilon := by
    norm_num [epsilon,SourcePrimeBands.epsilon,SourcePrimeBands.eta]
  filter_upwards [h1.eventually (eventually_gt_nhds hlt),h2.eventually (eventually_lt_nhds hgt),
    eventually_gt_atTop (1 : ℝ)] with B hb1 hb2 hB
  have hl : 0 < Real.log B := Real.log_pos hB
  rw [source_harmonicCenter]
  constructor
  · have : epsilon/10 < (theta/2 * SourcePrimeBands.centerMass B) / Real.log B := by
      simpa only [mul_div_assoc] using hb1
    exact ((lt_div_iff₀ hl).mp this).le
  · have : (theta * SourcePrimeBands.centerMass B) / Real.log B < epsilon := by
      simpa only [mul_div_assoc] using hb2
    exact ((div_lt_iff₀ hl).mp this).le

theorem source_center_exponential :
    ∀ᶠ B : ℝ in atTop, ∀ (g b : ℕ),
      Real.exp (-theta/2 * (sourceSystem B).harmonicCenter * g +
        theta * (sourceSystem B).harmonicCenter * b) ≤
      B ^ (-(epsilon/10)*(g : ℝ) + epsilon * b) := by
  filter_upwards [center_saving_coefficients,eventually_gt_atTop (1 : ℝ)] with B hB hB1
  intro g b
  rw [Real.rpow_def_of_pos (by linarith : 0 < B)]
  apply Real.exp_le_exp.mpr
  have hg := mul_le_mul_of_nonneg_right hB.1 (Nat.cast_nonneg g)
  have hb := mul_le_mul_of_nonneg_right hB.2 (Nat.cast_nonneg b)
  nlinarith only [hg,hb]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
