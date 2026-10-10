import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessErrorBelowTrace
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DensitySizeLeTestSize
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisconnectedErrorSum
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PostGapErrorSum
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapPrefactor
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceDisconnectedCertificatesSmall

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
open Finset Classical Filter
noncomputable section
namespace NumericalLine

theorem source_full_trace_raw (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+2*eta)*(sourceLength B:ℝ))+6*Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_retained_allowed_with_witness_majorant h hh τ T C₀ 32 hτ hC₀ (by norm_num),
    source_witness_majorant_small h hh τ C₀ hτ2 hC₀,
    source_unlit_tail_small h τ T C₀ hC₀,
    source_packed_gap_small h hh τ T C₀ hC₀,
    source_postGap_le_two_errors h hh τ T C₀,
    source_corrupted_small h hh τ T C₀ (zero_le_one.trans hτ) hC₀,
    source_disconnected_small h hh τ T C₀ (zero_le_one.trans hτ) hC₀] with B hr hw hu hp hg hc hd
  intro D cut
  have hf := fullTraceSum_le_retained_add_discarded (h:=h) (ℓ:=sourceLength B) (L:=pathLength B)
    D cut (sourceRetained hh 32)
  change fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
    sourceAllowedRetainedSum D hh 32 cut+discardedTraceSum D h (sourceLength B) (pathLength B) cut (sourceRetained hh 32) at hf
  have h₁ := discarded_le_unlit_add_geometric D (ℓ:=sourceLength B) hh 32 cut
  have h₂ := geometric_le_packed_add_postGap D (ℓ:=sourceLength B) hh 32 cut
  linarith [hr D cut,hw D,hu D cut,hp D cut,hg D cut,hc D cut,hd D cut]

theorem source_high_trace (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_full_trace_raw h hh τ T C₀ hτ hτ2 hC₀,
    source_witness_error_below_trace,source_one_exponential,eventually_ge_atTop (6:ℝ)] with B ht he hp hB
  intro D cut
  have hB0 : 0<B := by linarith
  have hseven : (7:ℝ)≤B^(eta*(sourceLength B:ℝ)) := by
    apply le_trans _ hp
    have := Real.add_one_le_exp B
    linarith
  calc
    _ ≤ B^(-(1+2*eta)*(sourceLength B:ℝ))+6*Real.exp (-B^(1+epsilon/2)) := ht D cut
    _ ≤ 7*B^(-(1+2*eta)*(sourceLength B:ℝ)) := by linarith
    _ ≤ B^(eta*(sourceLength B:ℝ))*B^(-(1+2*eta)*(sourceLength B:ℝ)) :=
      mul_le_mul_of_nonneg_right hseven (Real.rpow_nonneg hB0.le _)
    _ = _ := by rw [←Real.rpow_add hB0]; congr 1; ring

theorem source_high_trace_and_density (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) (κ : ℝ) (hκ : 0<κ) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      deletedDensity D h (pathLength B) ≤ (sourceMinPrime B)^(-1+κ) ∧
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_high_trace h hh τ T C₀ hτ hτ2 hC₀,
    source_deleted_density h τ C₀ κ hC₀ hκ] with B ht hd
  exact fun D cut => ⟨hd D,ht D cut⟩

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
