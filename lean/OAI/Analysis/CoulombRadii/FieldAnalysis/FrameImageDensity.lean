import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoreCoulombPotential
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

section
variable {X E Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]

omit [SeparableSpace E] in
lemma frame_spectral_l2image_hasSum {μ : Measure X} {ν : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i)‖^2)
      (∫ x, ‖B (v x)‖^2 ∂μ) := by
  let I := (exists_hilbertBasis ℂ (Lp ℂ 2 ν)).choose
  let c : HilbertBasis I ℂ (Lp ℂ 2 ν) := (exists_hilbertBasis ℂ (Lp ℂ 2 ν)).choose_spec.choose
  let : Countable I := orthonormal_countable c.orthonormal
  exact frameOperator_spectral_image_hasSum hv B c

omit [SeparableSpace E] in
lemma frame_spectral_l2image_submeasure_trace {μ : Measure X} {ν η : Measure Y}
    [SeparableSpace (Lp ℂ 2 η)] {v : X → E} (hv : MemLp v 2 μ)
    (B : E →L[ℂ] Lp ℂ 2 ν) (hη : η ≤ ν) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * (∫ y, ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i) y‖^2 ∂η))
      (∫ x, ∫ y, ‖B (v x) y‖^2 ∂η ∂μ) := by
  have h := frame_spectral_l2image_hasSum hv ((l2MeasureInclusion hη).comp B)
  simpa only [ContinuousLinearMap.comp_apply, l2MeasureInclusion_norm_sq] using h

noncomputable def frameImageDensity {μ : Measure X} {ν : Measure Y}
    {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) (y : Y) : ℝ :=
  ∑' i : Σ z, eigenspaceBasisSet (frameOperator μ v) z,
    i.1.re * ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
      (frameOperator_symmetric hv) i) y‖^2

lemma frameImageDensity_integrable {μ : Measure X} {ν : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) :
    Integrable (frameImageDensity hv B) ν := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  exact (l2_weighted_density_integrable (fun i => B (b i)) (fun i => i.1.re)
    (compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv))
    (frame_spectral_l2image_hasSum hv B).summable).1

lemma frameImageDensity_eq_ae {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [MeasurableSpace.CountablyGenerated Y]
    {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) (V : X → Y → ℂ)
    (hV : ∀ x, B (v x) =ᵐ[ν] V x)
    (hI : Integrable (fun xy : X × Y => ‖V xy.1 xy.2‖^2) (μ.prod ν)) :
    frameImageDensity hv B =ᵐ[ν] (fun y => ∫ x, ‖V x y‖^2 ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  have hsum := (frame_spectral_l2image_hasSum hv B).summable
  have hpos := compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (frameImageDensity_integrable hv B)
    hI.integral_prod_right
  intro A hA _
  have h1 := l2_weighted_density_setIntegral (fun i => B (b i)) (fun i => i.1.re) hpos hsum A
  have h2 := frame_spectral_l2image_submeasure_trace hv B (Measure.restrict_le_self (s := A))
  have he := h1.unique h2
  change (∫ y in A, frameImageDensity hv B y ∂ν) = ∫ x, ∫ y in A, ‖B (v x) y‖^2 ∂ν ∂μ at he
  rw [he]
  have hre : (∫ x, ∫ y in A, ‖B (v x) y‖^2 ∂ν ∂μ) =
      ∫ x, ∫ y in A, ‖V x y‖^2 ∂ν ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [(hV x).restrict] with y hy
    rw [hy]
  rw [hre]
  apply integral_integral_swap
  exact hI.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
end

variable {X E Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]

lemma frameImage_weighted_trace {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [MeasurableSpace.CountablyGenerated Y]
    {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) (V : X → Y → ℂ)
    (hV : ∀ x, B (v x) =ᵐ[ν] V x)
    (hI : Integrable (fun xy : X × Y => ‖V xy.1 xy.2‖^2) (μ.prod ν))
    (W : Y → ℝ) (hW : AEStronglyMeasurable W ν) (hWp : ∀ y, 0 ≤ W y)
    (hWI : Integrable (fun xy : X × Y => W xy.2 * ‖V xy.1 xy.2‖^2) (μ.prod ν)) :
    (∀ i : Σ z, eigenspaceBasisSet (frameOperator μ v) z, i.1.re ≠ 0 →
      Integrable (fun y => W y * ‖B (compactSpectralBasis (frameOperator μ v)
        (frameOperator_compact hv) (frameOperator_symmetric hv) i) y‖^2) ν) ∧
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ∫ y, W y * ‖B (compactSpectralBasis (frameOperator μ v)
        (frameOperator_compact hv) (frameOperator_symmetric hv) i) y‖^2 ∂ν)
      (∫ x, ∫ y, W y * ‖V x y‖^2 ∂ν ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  have hpos := compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)
  have hsum := (frame_spectral_l2image_hasSum hv B).summable
  have hae := frameImageDensity_eq_ae hv B V hV hI
  have ht : (fun y => W y * frameImageDensity hv B y) =ᵐ[ν]
      (fun y => ∫ x, W y * ‖V x y‖^2 ∂μ) := by
    filter_upwards [hae] with y hy
    rw [hy, integral_const_mul]
  have hint : Integrable (fun y => W y * frameImageDensity hv B y) ν :=
    hWI.integral_prod_right.congr ht.symm
  have hF (i : Σ z, eigenspaceBasisSet (frameOperator μ v) z) :
      AEStronglyMeasurable (fun y => i.1.re * ‖B (b i) y‖^2) ν :=
    ((Lp.aestronglyMeasurable (B (b i))).norm.pow 2).const_mul _
  have hp (i : Σ z, eigenspaceBasisSet (frameOperator μ v) z) (y : Y) :
      0 ≤ i.1.re * ‖B (b i) y‖^2 := mul_nonneg (hpos i) (sq_nonneg _)
  have hi := weighted_series_integrable_hasSum hF hp
    (l2_weighted_density_integrable (fun i => B (b i)) (fun i => i.1.re) hpos hsum).2 hW hWp hint
  constructor
  · intro i hi0
    have H := (hi.1 i).const_mul (i.1.re)⁻¹
    convert H using 1
    ext y
    dsimp only [b]
    field_simp
  · convert hi.2 using 1
    · funext i
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    · change (∫ x, ∫ y, W y * ‖V x y‖^2 ∂ν ∂μ) =
        ∫ y, W y * frameImageDensity hv B y ∂ν
      rw [integral_congr_ae ht]
      exact integral_integral_swap hWI
end Coulomb

open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate

end

end OAI
