import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RepeatedUnlitTotalEqFixed
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllCoreLit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PostGapErrorSum
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ComponentBoundAfterGap

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

def disconnectedErrorSum {B τ T C₀ : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    {h ℓ : ℕ} (hh : 0<h) (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ,avg (fun r : (sourceSystem B).Residues =>
    if AllCoreLit w.line ((sourceSystem B).binarySplit w.line r).1 ∧
      NoFixedForbidden w.line D (pathLength B) ((sourceSystem B).binarySplit w.line r).1 ∧
      repeatedUnlitTotal w.line r<listCutoff B ∧
      ¬Nonempty (GapFamily w ((sourceSystem B).binarySplit w.line r).1 (pathLength B) (listCutoff B)) ∧
      B^(1-2*rho) ≤ (disconnectedCount w.line hh ((sourceSystem B).binarySplit w.line r).1:ℝ) then
        |(sourceSystem B).chronologicalKernel w.line cut r*allowedIndicator w.line D (pathLength B) r|
    else 0)

def corruptedErrorSum {B τ T C₀ : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    {h ℓ : ℕ} (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ,avg (fun r : (sourceSystem B).Residues =>
    if B^(1-2*rho) ≤ (corruptedCount (sourceSystem B) w.line:ℝ) then
      |(sourceSystem B).chronologicalKernel w.line cut r*allowedIndicator w.line D (pathLength B) r|
    else 0)

theorem source_postGap_le_two_errors (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      postGapErrorSum D (ℓ:=sourceLength B) hh 32 cut ≤
        disconnectedErrorSum D (ℓ:=sourceLength B) hh cut+corruptedErrorSum D (h:=h) (ℓ:=sourceLength B) cut := by
  filter_upwards [source_components_after_gap h hh τ C₀] with B hcomp
  intro D cut
  unfold postGapErrorSum disconnectedErrorSum corruptedErrorSum
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro w hw
  rw [←OrdinaryCorrelations.SourceCylinder.avg_add']
  apply avg_mono
  intro r
  let a := ((sourceSystem B).binarySplit w.line r).1
  by_cases hg : (AllCoreLit w.line a ∧ NoFixedForbidden w.line D (pathLength B) a ∧
      repeatedUnlitTotal w.line r<listCutoff B ∧ ¬sourceRetained hh 32 w a) ∧
      ¬Nonempty (GapFamily w a (pathLength B) (listCutoff B))
  · rw [ite_eq_left hg]
    have huc : repeatedCenterUnlitCount w.line a<listCutoff B := by
      rw [←repeatedUnlitTotal_eq_fixed]; exact hg.1.2.2.1
    have hcomponents := hcomp D w a hg.1.1 huc hg.2
    by_cases hd : B^(1-2*rho) ≤ (disconnectedCount w.line hh a:ℝ)
    · rw [ite_eq_left ⟨hg.1.1,hg.1.2.1,hg.1.2.2.1,hg.2,hd⟩]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · have hcor : B^(1-2*rho) ≤ (corruptedCount (sourceSystem B) w.line:ℝ) := by
        by_contra hc
        apply hg.1.2.2.2
        refine ⟨⟨hg.1.1,huc,?_,lt_of_not_ge hd,lt_of_not_ge hc⟩,hg.1.2.1⟩
        intro p hp
        exact hcomponents p
      rw [ite_eq_left hcor]
      exact le_add_of_nonneg_left (by split_ifs <;> positivity)
  · rw [ite_eq_right hg]
    apply add_nonneg <;> split_ifs <;> positivity

theorem source_full_trace_two_errors (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ<2) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+2*Real.exp (-B^(1+epsilon/2))+
          disconnectedErrorSum D (ℓ:=sourceLength B) hh cut+
          corruptedErrorSum D (h:=h) (ℓ:=sourceLength B) cut := by
  filter_upwards [source_full_trace_with_postGap h hh τ T C₀ 32 hτ hτ2 hC₀ (by norm_num),
    source_postGap_le_two_errors h hh τ T C₀] with B ht he
  intro D cut
  linarith [ht D cut,he D cut]

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
