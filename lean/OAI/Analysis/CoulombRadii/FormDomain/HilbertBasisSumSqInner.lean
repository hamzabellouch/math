import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FrameOperator
import OAI.Analysis.CoulombRadii.SpectralTheory.EigenspaceBasisSet

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
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma hilbertBasis_hasSum_sq_inner {ι : Type*} (b : HilbertBasis ι ℂ E) (u : E) :
    HasSum (fun i => ‖inner ℂ (b i) u‖^2) (‖u‖^2) := by
  have h := (b.hasSum_inner_mul_inner u u).mapL Complex.reCLM
  convert h using 1
  · ext i
    rw [← inner_conj_symm u (b i), ← Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.sq_norm (inner ℂ (b i) u)
  · rw [inner_self_eq_norm_sq_to_K]
    change ‖u‖^2 = ((‖u‖ : ℂ)^2).re
    rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma frameOperator_hasSum_diagonal {ι : Type*} [Countable ι]
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (b : HilbertBasis ι ℂ E) :
    HasSum (fun i => (inner ℂ (b i) (frameOperator μ v (b i))).re)
      (∫ x, ‖v x‖^2 ∂μ) := by
  have hs (x : X) := hilbertBasis_hasSum_sq_inner b (v x)
  have hh : HasSum (fun i => ∫ x, ‖inner ℂ (b i) (v x)‖^2 ∂μ)
      (∫ x, ‖v x‖^2 ∂μ) := by
    apply hasSum_integral_of_dominated_convergence (fun i x => ‖inner ℂ (b i) (v x)‖^2)
    · intro i
      exact (((innerSL ℂ (b i)).continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable).norm.pow 2)
    · intro i
      exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)])
    · exact Filter.Eventually.of_forall (fun x => (hs x).summable)
    · simp_rw [(hs _).tsum_eq]
      exact hv.integrable_norm_pow (by norm_num)
    · exact Filter.Eventually.of_forall hs
  convert hh using 1
  ext i
  rw [frameOperator_quadratic hv]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_inner_symm]

lemma frameOperator_spectral_hasSum [SeparableSpace E]
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z => i.1.re)
      (∫ x, ‖v x‖^2 ∂μ) := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  convert frameOperator_hasSum_diagonal hv b using 1
  ext i
  simp [b, compactSpectralBasis_eigen,
    inner_self_eq_norm_sq_to_K, (compactSpectralBasis _ _ _).orthonormal.1 i]

lemma compactSpectralBasis_quadratic_hasSum (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) (u : E) :
    HasSum (fun i : Σ z, eigenspaceBasisSet T z =>
      i.1.re * ‖inner ℂ (compactSpectralBasis T hc hT i) u‖^2)
      (inner ℂ u (T u)).re := by
  let b := compactSpectralBasis T hc hT
  have h := (((b.hasSum_repr u).mapL T).mapL (innerSL ℂ u)).mapL Complex.reCLM
  convert h using 1
  · ext i
    have hi : i.1 = (i.1.re : ℂ) := Complex.ext rfl (by
      simpa only [Complex.ofReal_im] using compactSpectralBasis_eigen_real T hc hT i)
    simp only [ContinuousLinearMap.map_smul, innerSL_apply_apply,
      HilbertBasis.repr_apply_apply, b, compactSpectralBasis_eigen,
      Complex.reCLM_apply]
    rw [hi, ← inner_conj_symm (u) (compactSpectralBasis T hc hT i)]
    simp only [smul_eq_mul, Complex.ofReal_re]
    rw [show inner ℂ (compactSpectralBasis T hc hT i) u *
        ((i.1.re : ℂ) * conj (inner ℂ (compactSpectralBasis T hc hT i) u)) =
        (i.1.re : ℂ) * (conj (inner ℂ (compactSpectralBasis T hc hT i) u) *
        inner ℂ (compactSpectralBasis T hc hT i) u) by ring]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
    simp [-Complex.ofReal_pow]
  · rfl

end Coulomb

end

end OAI
