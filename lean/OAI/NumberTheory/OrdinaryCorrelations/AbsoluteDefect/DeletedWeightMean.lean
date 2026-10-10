import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalIndicator
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DensitySizeLeTestSize
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResiduesAdd
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AmplitudeSecondSum

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical Filter
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ}

def deletedWeightMean (D : S.DivisorFamily B τ C₀) (h L : ℕ) : ℝ :=
  avg (fun r => S.vertexWeight r 0*deletedIndicator D h L r)

theorem deletedWeightMean_bound (D : S.DivisorFamily B τ C₀) (h L : ℕ) :
    deletedWeightMean D h L ≤
      Real.sqrt (Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter))*
        Real.sqrt (deletedDensity D h L) := by
  have hc := vertexWeight_event_bound S 0
    (fun r => ∃ s : S.Specification D h L,s.Primitive ∧ ∀ p,s.ResidueTest p 0 (r p))
  have hc' : deletedWeightMean D h L ≤
      Real.sqrt (avg (fun r:S.Residues => S.vertexWeight r 0^2))*Real.sqrt (deletedDensity D h L) := by
    unfold deletedWeightMean deletedDensity deletedIndicator
    simp only [mul_ite,mul_one,mul_zero]
    convert hc using 1 <;> congr 1
    · funext r
      split_ifs <;> rfl
    · congr 1
      apply congrArg FiniteIntegration.avg
      funext r
      split_ifs <;> rfl
  exact hc'.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (vertexWeight_second_moment_source S 0)) (Real.sqrt_nonneg _))

theorem source_deleted_weight (h : ℕ) (τ C₀ κ : ℝ) (hC₀ : 0≤C₀) (hκ : 0<κ) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀),
      deletedWeightMean D h (pathLength B) ≤
        Real.sqrt (Real.exp ((A^2+2*A)*(sourceSystem B).harmonicCore+
          3*(sourceSystem B).harmonicCenter))*Real.sqrt ((sourceMinPrime B)^(-1+κ)) := by
  filter_upwards [source_deleted_density h τ C₀ κ hC₀ hκ] with B hB
  intro D
  exact (deletedWeightMean_bound D h (pathLength B)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hB D)) (Real.sqrt_nonneg _))

lemma deletedIndicator_integer (D : S.DivisorFamily B τ C₀) (h L : ℕ) (n : ℤ) :
    deletedIndicator D h L (S.integerResidues n)=if VertexAllowed D h L n then 0 else 1 := by
  by_cases hn : VertexAllowed D h L n
  · simp only [hn,ite_true]
    exact (deletedIndicator_integer_zero (D:=D) (h:=h) (L:=L) n).mpr hn
  · simp only [hn,ite_false]
    have hz : deletedIndicator D h L (S.integerResidues n)≠0 := by
      exact mt (deletedIndicator_integer_zero (D:=D) (h:=h) (L:=L) n).mp hn
    unfold deletedIndicator at hz ⊢
    split_ifs at hz ⊢ <;> tauto

theorem real_deleted_weight_tendsto (D : S.DivisorFamily B τ C₀) (h L : ℕ) (z : ℝ → ℤ) :
    Tendsto (fun X:ℝ => (∑ n∈range ⌊X⌋₊,
      if VertexAllowed D h L ((n:ℤ)+z X) then 0
      else S.vertexWeight (S.integerResidues ((n:ℤ)+z X)) 0)/X)
      atTop (nhds (deletedWeightMean D h L)) := by
  have ht := S.real_origin_tendsto
    (fun r => S.vertexWeight r 0*deletedIndicator D h L r) z
  simpa only [deletedIndicator_integer,mul_ite,mul_zero,mul_one,deletedWeightMean] using ht

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
