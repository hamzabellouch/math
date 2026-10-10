import Mathlib

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
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
namespace Coulomb
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]

lemma l2_kernel_integral (v : X → Lp ℂ 2 ν) (hv : MemLp v 2 μ)
    (V : X → Y → ℂ) (hV : ∀ t, (v t : Y → ℂ) =ᵐ[ν] V t)
    (hK : MemLp (fun z : X × Y => V z.1 z.2) 2 (μ.prod ν))
    (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hC : ∀ t, ‖c t‖ ≤ C)
    (hF : MemLp (fun y => ∫ t, c t*V t y ∂μ) 2 ν) :
    (∫ t, c t • v t ∂μ) = hF.toLp (fun y => ∫ t, c t*V t y ∂μ) := by
  have hctop : MemLp c ∞ μ := memLp_top_of_bound hc C (Filter.Eventually.of_forall hC)
  have hcv : MemLp (fun t => c t • v t) 2 μ := hctop.smul hv
  have hi := hcv.integrable (by norm_num)
  have hcprod : MemLp (fun z : X × Y => c z.1) ∞ (μ.prod ν) :=
    memLp_top_of_bound hc.comp_fst C (Filter.Eventually.of_forall (fun z => hC z.1))
  have hcvprod : MemLp (fun z : X × Y => c z.1*V z.1 z.2) 2 (μ.prod ν) := hcprod.fun_mul hK
  apply ext_inner_left ℂ
  intro w
  have hw : MemLp (fun z : X × Y => star (w z.2)) 2 (μ.prod ν) :=
    (Lp.memLp w).star.comp_snd μ
  have hint : Integrable (fun z : X × Y => star (w z.2)*(c z.1*V z.1 z.2)) (μ.prod ν) := by
    exact memLp_one_iff_integrable.mp (hw.fun_mul hcvprod)
  calc
    inner ℂ w (∫ t, c t • v t ∂μ) = ∫ t, inner ℂ w (c t • v t) ∂μ := by
      exact ((innerSL ℂ w).integral_comp_comm hi).symm
    _ = ∫ t, ∫ y, star (w y)*(c t*V t y) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hV t] with y hy
      simp only [RCLike.inner_apply', starRingEnd_apply, hy]
      ring
    _ = ∫ y, ∫ t, star (w y)*(c t*V t y) ∂μ ∂ν := integral_integral_swap hint
    _ = ∫ y, star (w y)*(∫ t, c t*V t y ∂μ) ∂ν := by simp only [integral_const_mul]
    _ = inner ℂ w (hF.toLp _) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with y hy
      simp only [RCLike.inner_apply', starRingEnd_apply, hy]
end Coulomb

end

end OAI
