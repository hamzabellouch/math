import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AffineResidueEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceFullTraceRaw

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
variable {S : PrimeSystem} {B τ C₀ : ℝ}

def fullArithmeticTrace {T : ℝ} (D : S.DivisorFamily B τ C₀)
    (h ℓ L : ℕ) (cut : S.Cutoffs T) (q : ℕ) (z : ℝ → ℤ) (X : ℝ) : ℝ :=
  ∑ w : NumericalLine D h ℓ, |(∑ m ∈ range ⌊X⌋₊,
    S.chronologicalKernel w.line cut (S.integerResidues (q*(m:ℤ)+z X)) *
      allowedIndicator w.line D L (S.integerResidues (q*(m:ℤ)+z X)))/X|

theorem fullArithmeticTrace_tendsto {T : ℝ} (D : S.DivisorFamily B τ C₀)
    (h ℓ L : ℕ) (cut : S.Cutoffs T) (q : ℕ)
    (hq : ∀ p : S.Index,Nat.Coprime q (p:ℕ)) (z : ℝ → ℤ) :
    Tendsto (fullArithmeticTrace D h ℓ L cut q z) atTop
      (nhds (fullTraceSum D h ℓ L cut)) := by
  unfold fullArithmeticTrace fullTraceSum
  apply tendsto_finsetSum
  intro w hw
  exact (S.real_affine_origin_tendsto (fun r => S.chronologicalKernel w.line cut r*
    allowedIndicator w.line D L r) q hq z).abs

theorem source_full_arithmetic_trace (h q : ℕ) (hh : 0<h) (hq : 0<q)
    (τ T C₀ : ℝ) (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T) (z : ℝ → ℤ) (δ : ℝ),0<δ →
      ∀ᶠ X : ℝ in atTop,
      fullArithmeticTrace D h (sourceLength B) (pathLength B) cut q z X ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+δ := by
  filter_upwards [source_high_trace h hh τ T C₀ hτ hτ2 hC₀,
    source_eventually_coprime q hq] with B ht hc
  intro D cut z δ hδ
  have hlim := fullArithmeticTrace_tendsto D h (sourceLength B) (pathLength B) cut q hc z
  exact hlim.eventually (eventually_le_nhds (lt_add_of_le_of_pos (ht D cut) hδ))

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
