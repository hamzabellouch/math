import Mathlib.Analysis.Calculus.Deriv.Slope
import OAI.NumberTheory.Jacobsthal.Analysis.SourceProductLimit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
attribute [local instance] Classical.propDecidable
open ErdosCorrectionLimit
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.ReferenceDifferentiation
open NumberTheoryLean.ReferenceLocalResidual NumberTheoryLean.ReferenceMertens

theorem starting_extension_derivative_two :
    HasDerivAt (startingExtension sieveA) (Real.exp Real.eulerMascheroniConstant) 2 := by
  have hh := startingExtension_hasDerivAt (s := 2) (by norm_num)
  convert! hh using 1
  norm_num [evenInitial,sieveA]
  ring

theorem starting_extension_two : startingExtension sieveA 2=0 := by norm_num [startingExtension]

noncomputable def startingSlope (s : ℝ) : ℝ :=
  Function.update (fun t => (startingExtension sieveA t-startingExtension sieveA 2)/(t-2))
    2 (Real.exp Real.eulerMascheroniConstant) s

theorem startingSlope_continuousAt : ContinuousAt startingSlope 2 :=
  starting_extension_derivative_two.continuousAt_div

theorem startingSlope_two : startingSlope 2=Real.exp Real.eulerMascheroniConstant := by simp [startingSlope]

theorem starting_extension_factor (s : ℝ) : startingExtension sieveA s=startingSlope s*(s-2) := by
  by_cases hs : s=2
  · subst s
    simp only [starting_extension_two,sub_self,mul_zero]
  · rw [startingSlope,Function.update_of_ne hs,starting_extension_two,sub_zero]
    exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hs)).symm

theorem root_startingSlope_tendsto (a : ℝ) :
    Tendsto (fun z => startingSlope (sourceRootNode a z).ratio) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  simpa only [startingSlope_two] using! startingSlope_continuousAt.tendsto.comp (actual_root_ratio_tendsto a)

theorem root_parentBenchmark_tendsto (a : ℝ) :
    Tendsto (fun z => ErdosInverseBoxHeight.sourceB z*parentBenchmark .even (sourceRootNode a z).ratio) atTop
      (𝓝 (-a*Real.exp Real.eulerMascheroniConstant)) := by
  have hh := (root_startingSlope_tendsto a).mul (actual_root_centered_gap_tendsto a)
  rw [show Real.exp Real.eulerMascheroniConstant*(-a)=-a*Real.exp Real.eulerMascheroniConstant by ring] at hh
  apply hh.congr'
  filter_upwards [actual_root_eventually a] with z hs
  have hr4 : (sourceRootNode a z).ratio ≤ 4 := by linarith [hs.2.2.2.2.1]
  rw [parent_even_eq_starting hr4,starting_extension_factor]
  have hratio : (sourceRootNode a z).ratio=(sourceRootNode a z).gap/ErdosInverseBoxHeight.sourceB z := rfl
  rw [hratio]
  have hB0 : ErdosInverseBoxHeight.sourceB z ≠ 0 := hs.1.ne'
  field_simp

theorem root_nodeBenchmark_tendsto (a : ℝ) :
    Tendsto (fun z => (ErdosInverseBoxHeight.sourceB z)^2*
      nodeBenchmark (ErdosInverseBoxHeight.sourceW z) (sourceRootNode a z)) atTop
      (𝓝 (-a*Real.exp Real.eulerMascheroniConstant)) := by
  have hh := (root_referenceProduct_tendsto true).mul (root_parentBenchmark_tendsto a)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards with z
  change ErdosInverseBoxHeight.sourceB z*referenceProduct (ErdosInverseBoxHeight.sourceW z)
      (ErdosInverseBoxHeight.sourceB z) true*(ErdosInverseBoxHeight.sourceB z*parentBenchmark .even (sourceRootNode a z).ratio)=
    (ErdosInverseBoxHeight.sourceB z)^2*(referenceProduct (ErdosInverseBoxHeight.sourceW z)
      (ErdosInverseBoxHeight.sourceB z) true*parentBenchmark .even (sourceRootNode a z).ratio)
  ring

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
