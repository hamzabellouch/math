import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RepeatedUnlitTotalEqFixed
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FarTestSizePolynomial
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisconnectedCertificate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessBaseDoublePath

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.NumericalSubtrees Finset Classical Filter
noncomputable section
namespace NumericalLine
theorem source_disconnected_certificates_small (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ) (hτ : 0≤τ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      disconnectedCertificateSum D hh (sourceLength B) (pathLength B) (listCutoff B) (farRootBudget B C₀ τ h) cut ≤
        Real.exp (-B^(1+epsilon/2)) := by
  have hC : 0≤C₀+4*(h:ℝ)*τ := by positivity
  filter_upwards [source_double_path_prefactor C₀ hC₀,
    source_far_delta_saving C₀ τ h hC,source_far_root_small C₀ τ h hC,
    eventually_const_mul_rpow_le (1+epsilon/2) (1+3*epsilon) 6 (by norm_num [epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hpref hdelta hroot hdom hB
  intro D cut
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hP : 0<sourceMinPrime B := Real.exp_pos _
  have htpos : 0<listCutoff B := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hB0 _)
  have hb := disconnectedCertificateSum_bound (D:=D) (ℓ:=sourceLength B) (L:=pathLength B)
    (t:=listCutoff B) (R:=farRootBudget B C₀ τ h) hh cut (sourceMinPrime B) hP hB0.le hτ
    (sourceLength_le B hB0.le) (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩)
  have ht : B^(4*epsilon) ≤ (listCutoff B:ℝ) := Nat.le_ceil _
  have hs : (1/2)*B^(1+3*epsilon) ≤ (listCutoff B:ℝ)*((1/2)*B^(1-epsilon)) := by
    have hm := mul_le_mul_of_nonneg_right ht (show 0≤(1/2)*B^(1-epsilon) by positivity)
    have he : B^(4*epsilon)*((1/2)*B^(1-epsilon))=(1/2)*B^(1+3*epsilon) := by
      rw [mul_left_comm,←Real.rpow_add hB0]
      congr 2
      ring
    rwa [he] at hm
  have hδ0 : 0 ≤ max (farTestSize B C₀ τ h/(sourceMinPrime B*Real.log 2)) ((2+B)/sourceMinPrime B) :=
    le_trans (by positivity : 0≤(2+B)/sourceMinPrime B) (le_max_right _ _)
  apply hb.trans
  apply (mul_le_mul (mul_le_mul hroot hpref (by unfold packedGapPrefactor; positivity [A_pos]) (Real.exp_pos _).le)
    (pow_le_pow_left₀ hδ0 hdelta _) (pow_nonneg hδ0 _) (by positivity)).trans
  rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem source_disconnected_small (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ) (hτ : 0≤τ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      disconnectedErrorSum D (ℓ:=sourceLength B) hh cut ≤ Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_disconnected_certificates_small h hh τ T C₀ hτ hC₀,
    source_disconnected_threshold C₀ hC₀,source_component_budget,source_eventually_large h,
    eventually_ge_atTop (1:ℝ)] with B hsmall hthreshold hcomp hlarge hB
  intro D cut
  apply le_trans _ (hsmall D cut)
  unfold disconnectedErrorSum disconnectedCertificateSum
  apply sum_le_sum
  intro w hw
  apply avg_mono
  intro r
  split_ifs with hex hc
  · exact le_refl _
  · exfalso
    apply hc
    have htpos : 0<listCutoff B := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) _)
    apply w.disconnectedCertificate_exists hh ((sourceSystem B).binarySplit w.line r).1 hcomp.1 htpos
      hex.1 _ hex.2.2.2.1 (fun p => Nat.not_dvd_of_pos_of_lt hh (hlarge.2 p).2)
      (Nat.cast_le.mp (hthreshold.trans hex.2.2.2.2)) hτ (sourceLength_le B (zero_le_one.trans hB))
    rw [←repeatedUnlitTotal_eq_fixed]
    exact hex.2.2.1
  · positivity
  · exact le_refl _

theorem source_full_common_residue_trace (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+5*Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_full_trace_disconnected h hh τ T C₀ hτ hτ2 hC₀,
    source_disconnected_small h hh τ T C₀ (zero_le_one.trans hτ) hC₀] with B hfull hdisc
  intro D cut
  linarith [hfull D cut,hdisc D cut]

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
