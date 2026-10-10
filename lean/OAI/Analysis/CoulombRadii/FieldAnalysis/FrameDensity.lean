import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.IntegrableTsumSummableNormIntegral
import OAI.Analysis.CoulombRadii.FormDomain.L2WeightedDensitySetIntegral

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def frameDensity {μ : Measure X} {ν : Measure Y}
    {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) (y : Y) : ℝ :=
  ∑' i : Σ z, eigenspaceBasisSet (frameOperator μ v) z,
    i.1.re * ‖compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
      (frameOperator_symmetric hv) i y‖^2

lemma frameDensity_integrable {μ : Measure X} {ν : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) :
    Integrable (frameDensity hv) ν := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  apply (l2_weighted_density_integrable b (fun i => i.1.re)
    (compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)) _).1
  simpa only [b.orthonormal.1, one_pow, mul_one] using (frameOperator_spectral_hasSum hv).summable

lemma frameDensity_eq_ae {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [MeasurableSpace.CountablyGenerated Y]
    {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) (V : X → Y → ℂ)
    (hV : ∀ x, v x =ᵐ[ν] V x)
    (hI : Integrable (fun xy : X × Y => ‖V xy.1 xy.2‖^2) (μ.prod ν)) :
    frameDensity hv =ᵐ[ν] (fun y => ∫ x, ‖V x y‖^2 ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  have hsum : Summable (fun i => i.1.re * ‖b i‖^2) := by
    simpa only [b.orthonormal.1, one_pow, mul_one] using (frameOperator_spectral_hasSum hv).summable
  have hpos := compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (frameDensity_integrable hv)
    hI.integral_prod_right
  intro A hA _
  have h1 := l2_weighted_density_setIntegral b (fun i => i.1.re) hpos hsum A
  have h2 := frame_l2_submeasure_trace hv (Measure.restrict_le_self (s := A))
  have he := h1.unique h2
  change (∫ y in A, frameDensity hv y ∂ν) = ∫ x, ∫ y in A, ‖v x y‖^2 ∂ν ∂μ at he
  rw [he]
  have hre : (∫ x, ∫ y in A, ‖v x y‖^2 ∂ν ∂μ) =
      ∫ x, ∫ y in A, ‖V x y‖^2 ∂ν ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [(hV x).restrict] with y hy
    rw [hy]
  rw [hre]
  apply integral_integral_swap
  exact hI.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
end Coulomb

end

end OAI
