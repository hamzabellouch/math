import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.HilbertBasisSumSqInner

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma hasSum_swap_nonnegative {ι κ : Type*} {f : ι × κ → ℝ}
    (hf : ∀ i, 0 ≤ f i) {r : ι → ℝ} {c : κ → ℝ} {s : ℝ}
    (hr : ∀ i, HasSum (fun j => f (i,j)) (r i))
    (hc : ∀ j, HasSum (fun i => f (i,j)) (c j)) (hs : HasSum r s) : HasSum c s := by
  have her : (fun i => ∑' j, f (i,j)) = r := funext (fun i => (hr i).tsum_eq)
  have hec : (fun j => ∑' i, f (i,j)) = c := funext (fun j => (hc j).tsum_eq)
  have hf' : Summable f := (summable_prod_of_nonneg hf).mpr
    ⟨fun i => (hr i).summable, by rw [her]; exact hs.summable⟩
  have hh := hf'.prod_symm.prod.hasSum
  change HasSum (fun j => ∑' i, f (i,j)) (∑' j, ∑' i, f (i,j)) at hh
  rw [hec] at hh
  apply hh.summable.hasSum_iff.mpr
  calc
    (∑' j, c j) = ∑' j, ∑' i, f (i,j) := by rw [hec]
    _ = ∑' i, ∑' j, f (i,j) := (Summable.tsum_comm (f := fun i j => f (i,j)) hf')
    _ = s := by rw [her]; exact hs.tsum_eq

omit [SeparableSpace E] in
lemma frameOperator_spectral_image_quadratic_hasSum
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] F) (u : F) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ‖inner ℂ u (B (compactSpectralBasis (frameOperator μ v)
        (frameOperator_compact hv) (frameOperator_symmetric hv) i))‖^2)
      (inner ℂ u (frameOperator μ (fun x => B (v x)) u)).re := by
  have h := compactSpectralBasis_quadratic_hasSum (frameOperator μ v)
    (frameOperator_compact hv) (frameOperator_symmetric hv) (B.adjoint u)
  convert h using 1
  · ext i
    simp only [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  · have hB : MemLp (fun x => B (v x)) 2 μ := B.comp_memLp' hv
    rw [frameOperator_quadratic hB, frameOperator_quadratic hv]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ContinuousLinearMap.adjoint_inner_right]

omit [SeparableSpace E] in
lemma frameOperator_spectral_image_hasSum {ι : Type*} [Countable ι]
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ)
    (B : E →L[ℂ] F) (c : HilbertBasis ι ℂ F) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i)‖^2) (∫ x, ‖B (v x)‖^2 ∂μ) := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let f : ι × (Σ z, eigenspaceBasisSet (frameOperator μ v) z) → ℝ := fun ji =>
    ji.2.1.re * ‖inner ℂ (c ji.1) (B (b ji.2))‖^2
  refine hasSum_swap_nonnegative (f := f)
      (r := fun j => (inner ℂ (c j) (frameOperator μ (fun x => B (v x)) (c j))).re) ?_ ?_ ?_ ?_
  · intro ji
    exact mul_nonneg (compactSpectralBasis_eigen_nonneg (frameOperator μ v)
      (frameOperator_compact hv) (frameOperator_positive hv) ji.2) (sq_nonneg _)
  · intro j
    exact frameOperator_spectral_image_quadratic_hasSum hv B (c j)
  · intro i
    exact (hilbertBasis_hasSum_sq_inner c (B (b i))).mul_left i.1.re
  · exact frameOperator_hasSum_diagonal (B.comp_memLp' hv) c
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

end

end OAI
