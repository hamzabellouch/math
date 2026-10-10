import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.SumSwapNonnegative

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
variable {Y : Type*} [MeasurableSpace Y]

lemma l2_norm_sq (ν : Measure Y) (u : Lp ℂ 2 ν) :
    ‖u‖^2 = ∫ y, ‖u y‖^2 ∂ν := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

noncomputable def l2MeasureInclusion {ν η : Measure Y} (h : η ≤ ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 η where
  toFun := Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h)
  map_add' := by intro u v; exact map_add _ u v
  map_smul' := by
    intro z u
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) (z • u),
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) u),
      Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) u,
      (Measure.absolutelyContinuous_of_le h).ae_eq (Lp.coeFn_smul z u)] with y h1 h2 h3 h4
    simp only [h1, h2, h4, Pi.smul_apply, h3, RingHom.id_apply]
  cont := (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h)).continuous

lemma l2MeasureInclusion_coe {ν η : Measure Y} (h : η ≤ ν) (u : Lp ℂ 2 ν) :
    l2MeasureInclusion h u =ᵐ[η] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) u

lemma l2MeasureInclusion_norm_sq {ν η : Measure Y} (h : η ≤ ν) (u : Lp ℂ 2 ν) :
    ‖l2MeasureInclusion h u‖^2 = ∫ y, ‖u y‖^2 ∂η := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [l2MeasureInclusion_coe h u] with y hy
  rw [hy]
end

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma frame_l2_submeasure_trace {μ : Measure X} {ν η : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] [SeparableSpace (Lp ℂ 2 η)]
    {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) (hη : η ≤ ν) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * (∫ y, ‖compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i y‖^2 ∂η))
      (∫ x, ∫ y, ‖v x y‖^2 ∂η ∂μ) := by
  let I := (exists_hilbertBasis ℂ (Lp ℂ 2 η)).choose
  let c : HilbertBasis I ℂ (Lp ℂ 2 η) := (exists_hilbertBasis ℂ (Lp ℂ 2 η)).choose_spec.choose
  let : Countable I := orthonormal_countable c.orthonormal
  have h := frameOperator_spectral_image_hasSum hv (l2MeasureInclusion hη) c
  simpa only [l2MeasureInclusion_norm_sq] using h
end Coulomb

end

end OAI
