import OAI.Geometry.RCD.Sobolev.EuclideanConvolutionLaplacian

namespace OAI

/-! # Associativity for the compact scalar convolutions used in local smoothing -/

open MeasureTheory
open scoped Convolution
noncomputable section
namespace RegularPointCoordinates

theorem compact_scalar_convolution_assoc {n : ℕ} {f g k : Euclidean n → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hk : Continuous k)
    (hgs : HasCompactSupport g) (hks : HasCompactSupport k) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g) ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] k =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (g ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] k) := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hgc : Continuous ((fun x => ‖g x‖) ⋆[L,volume] (fun x => ‖k x‖)) := hks.norm.continuous_convolution_right L hg.norm.locallyIntegrable hk.norm
  have hgcs : HasCompactSupport ((fun x => ‖g x‖) ⋆[L,volume] (fun x => ‖k x‖)) := hgs.norm.convolution L hks.norm
  funext x
  apply convolution_assoc L L L L
    (fun a b c => mul_assoc a b c)
    hf.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (hgs.convolutionExists_right L hf.locallyIntegrable hg)
  · exact Filter.Eventually.of_forall
      (hks.norm.convolutionExists_right L hg.norm.locallyIntegrable hk.norm)
  · exact hgcs.convolutionExists_right L hf.norm.locallyIntegrable hgc x

theorem scalar_convolution_comm {n : ℕ} (f g : Euclidean n → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g =
      g ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f := by
  apply convolution_symm (ContinuousLinearMap.mul ℝ ℝ)
  ext; simp

end RegularPointCoordinates

end

end OAI
