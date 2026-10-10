import Mathlib
import OAI.Probability.GaussianInformation.Inverse.InverseMoments

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem inverse_volume_without_support : InverseVolumeStatement := by
  refine ⟨20,by norm_num,300,?_⟩
  intro d hd ν hprob hν u
  have : IsProbabilityMeasure ν := hprob
  have hd1 : 1 ≤ d := by omega
  have hk3 : 3 ≤ d/100 := by omega
  have hk : d/100 ≤ d := Nat.div_le_self _ _
  have hk100 : 100*(d/100) ≤ d := by omega
  have hα : 10*(d/100:ℕ) ≤ ((d:ℝ)-1)/2 := by
    have hh : 100*(d/100:ℕ) ≤ (d:ℝ) := by exact_mod_cast hk100
    have hd' : (300:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  change (∫⁻ z,rawInverse u z ∂Measure.pi (fun _ : Fin (d/100) => ν)) ≤ _
  exact (lintegral_raw_le hd1 hk3 hα ν hν u).trans (inverse_constants hd1 hk)

end AllScaleInverseVolume

end OAI
