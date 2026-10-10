import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketWindowed

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
lemma packetState_toL2_norm (g : 𝓢(Space,ℂ)) (y p : Space) :
    ‖(packetState g y p).toLp 2 volume‖ = ‖g.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp),
    SchwartzMap.norm_toLp' (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [packetState_integral_norm_sq]

lemma packetState_toL2_continuous (g : 𝓢(Space,ℂ)) :
    Continuous (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) := by
  rw [continuous_iff_continuousAt]
  intro yp₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun yp : Space × Space =>
      ‖(packetState g yp.1 yp.2).toLp 2 volume -
        (packetState g yp₀.1 yp₀.2).toLp 2 volume‖^2) := by
    simp only [norm_sub_sq (𝕜 := ℂ), packetState_toL2_norm, packetState_inner]
    exact (continuous_const.sub (continuous_const.mul
      (Complex.continuous_re.comp (packetAnalysis_continuous g (packetState g yp₀.1 yp₀.2))))).add continuous_const
  have h := hc.sqrt.continuousAt (x := yp₀)
  simpa only [ContinuousAt, Real.sqrt_sq (norm_nonneg _), sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    Real.sqrt_zero] using h

lemma schwartz_toL2_norm_sq (g : 𝓢(Space,ℂ)) :
    ‖g.toLp 2 volume‖^2 = ∫ x : Space, ‖g x‖^2 := by
  have h := congrArg Complex.re (SchwartzMap.inner_toL2_toL2_eq g g volume)
  rw [inner_self_eq_norm_sq_to_K] at h
  change ((‖g.toLp 2 volume‖ : ℂ)^2).re = (∫ x : Space, inner ℂ (g x) (g x)).re at h
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at h
  rw [h]
  change RCLike.re (∫ x : Space, inner ℂ (g x) (g x)) = _
  rw [← integral_re]
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  · convert ((g.memLp 2 volume).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).ofReal using 1
    ext x
    simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]

lemma packetState_toL2_memLp (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    MemLp (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) 2 μ :=
  MemLp.of_bound (packetState_toL2_continuous g).aestronglyMeasurable ‖g.toLp 2 volume‖
    (Filter.Eventually.of_forall fun yp => (packetState_toL2_norm g yp.1 yp.2).le)
end Coulomb

end

end OAI
