import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllCoreLit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapPrefactor

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

def postGapErrorSum {B τ T C₀ : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    {h ℓ : ℕ} (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ, avg (fun r : (sourceSystem B).Residues =>
    if (AllCoreLit w.line ((sourceSystem B).binarySplit w.line r).1 ∧
      NoFixedForbidden w.line D (pathLength B) ((sourceSystem B).binarySplit w.line r).1 ∧
      repeatedUnlitTotal w.line r < listCutoff B ∧
      ¬sourceRetained hh K₀ w ((sourceSystem B).binarySplit w.line r).1) ∧
      ¬Nonempty (GapFamily w ((sourceSystem B).binarySplit w.line r).1 (pathLength B) (listCutoff B)) then
        |(sourceSystem B).chronologicalKernel w.line cut r*allowedIndicator w.line D (pathLength B) r|
    else 0)

lemma geometric_le_packed_add_postGap {B τ T C₀ : ℝ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) {h ℓ : ℕ}
    (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) :
    geometricErrorSum D (ℓ := ℓ) hh K₀ cut ≤
      packedGapSum D h ℓ (pathLength B) (listCutoff B) cut +
        postGapErrorSum D (ℓ := ℓ) hh K₀ cut := by
  unfold geometricErrorSum packedGapSum postGapErrorSum
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro w hw
  rw [←OrdinaryCorrelations.SourceCylinder.avg_add']
  apply avg_mono
  intro r
  by_cases hg : AllCoreLit w.line ((sourceSystem B).binarySplit w.line r).1 ∧
      NoFixedForbidden w.line D (pathLength B) ((sourceSystem B).binarySplit w.line r).1 ∧
      repeatedUnlitTotal w.line r < listCutoff B ∧
      ¬sourceRetained hh K₀ w ((sourceSystem B).binarySplit w.line r).1
  · rw [ite_eq_left hg]
    by_cases hp : Nonempty (GapFamily w ((sourceSystem B).binarySplit w.line r).1 (pathLength B) (listCutoff B))
    · simp [hg,hp]
    · simp [hg,hp]
  · simp only [hg,false_and,ite_false,add_zero]
    split_ifs <;> positivity

theorem source_full_trace_with_postGap (h : ℕ) (hh : 0 < h) (τ T C₀ K₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ < 2) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+2*Real.exp (-B^(1+epsilon/2))+
          postGapErrorSum D (ℓ := sourceLength B) hh K₀ cut := by
  filter_upwards [source_full_trace_with_geometry h hh τ T C₀ K₀ hτ hτ2 hC₀ hK₀,
    source_packed_gap_small h hh τ T C₀ hC₀] with B ht hp
  intro D cut
  have hg := geometric_le_packed_add_postGap D (ℓ := sourceLength B) hh K₀ cut
  linarith [ht D cut,hp D cut]

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
