import OAI.Geometry.NodalSets.Charts.SphereDifferentialCoordinates
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasureInvariance

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance sphereEnergyFormLocal1 : MeasurableSpace Base := borel Base
local instance sphereEnergyFormLocal2 : BorelSpace Base := ⟨rfl⟩

def sphereEnergyDensity (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ) (p : Base) : ℝ :=
  roundTensorPerturbation a p (sphereDifferential v p) (sphereDifferential w p) - lam*b p*v p*w p

def sphereEnergyForm (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ) : ℝ :=
  ∫ p, sphereEnergyDensity a b lam v w p ∂sphereReferenceMeasure

lemma sphereEnergyDensity_chart (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w)
    (p : Base) (x : Yau.Jets.Coord) :
    sphereEnergyDensity a b lam v w (sphereChartCoordMap p x) =
      a (sphereChartCoordMap p x) * roundCoordFactor x *
        (∑ i, Yau.coordPartial (v ∘ sphereChartCoordMap p) x i *
          Yau.coordPartial (w ∘ sphereChartCoordMap p) x i) -
      lam*b (sphereChartCoordMap p x)*v (sphereChartCoordMap p x)*w (sphereChartCoordMap p x) := by
  rw [sphereEnergyDensity,roundTensorPerturbation_apply,roundCotangentTensor_differential_pair v w hv hw]
  ring

lemma sphereEnergyForm_chart (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (p : Base) :
    sphereEnergyForm a b lam v w = ∫ x, roundCoordDensity x *
      (a (sphereChartCoordMap p x)*roundCoordFactor x*
        (∑ i, Yau.coordPartial (v ∘ sphereChartCoordMap p) x i *
          Yau.coordPartial (w ∘ sphereChartCoordMap p) x i) -
      lam*b (sphereChartCoordMap p x)*v (sphereChartCoordMap p x)*w (sphereChartCoordMap p x)) := by
  rw [sphereEnergyForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,sphereEnergyDensity_chart a b lam v w hv hw]

lemma sphereEnergyForm_symm (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ) :
    sphereEnergyForm a b lam v w = sphereEnergyForm a b lam w v := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  simp only [sphereEnergyDensity,roundTensorPerturbation_apply]
  rw [roundCotangentTensor_symm p (sphereDifferential v p) (sphereDifferential w p)]
  ring

lemma spherePullback_compact_support (a : Base → ℝ) {Q : Set Yau.Jets.Coord}
    (hQ : IsCompact Q) (ha : tsupport a ⊆ seedSphereFromCoord '' Q) :
    HasCompactSupport (a ∘ seedSphereFromCoord) := by
  apply hQ.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hQ.isClosed
  intro x hx
  obtain ⟨y,hy,he⟩ := ha (subset_closure hx)
  have hxy := seedSphereFromCoord_measurableEmbedding.injective he
  exact hxy ▸ hy

lemma sphereEnergyDensity_integrable (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (v w : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    Integrable (sphereEnergyDensity a b lam v w) sphereReferenceMeasure := by
  rw [sphereReferenceMeasure_integrable_chart seedPoint]
  simp only [roundChartDensity_coord_eq,sphereEnergyDensity_chart a b lam v w hv hw]
  have ha' := spherePullback_smooth a ha seedPoint
  have hb' := spherePullback_smooth b hb seedPoint
  have hv' := spherePullback_smooth v hv seedPoint
  have hw' := spherePullback_smooth w hw seedPoint
  have hs : ContDiff ℝ ∞ (fun x ↦ ∑ i, Yau.coordPartial (v ∘ sphereChartCoordMap seedPoint) x i *
      Yau.coordPartial (w ∘ sphereChartCoordMap seedPoint) x i) := by
    apply ContDiff.sum
    intro i _
    exact ((hv'.fderiv_right (by simp)).clm_apply contDiff_const).mul
      ((hw'.fderiv_right (by simp)).clm_apply contDiff_const)
  have hsmooth := roundCoordDensity_smooth.mul
    (((ha'.mul roundCoordFactor_smooth).mul hs).sub ((((contDiff_const (c := lam)).mul hb').mul hv').mul hw'))
  apply hsmooth.continuous.integrable_of_hasCompactSupport
  have hac : HasCompactSupport (fun x ↦ a (sphereChartCoordMap seedPoint x)) :=
    spherePullback_compact_support a hQ haQ
  have hbc : HasCompactSupport (fun x ↦ b (sphereChartCoordMap seedPoint x)) :=
    spherePullback_compact_support b hQ hbQ
  exact ((hac.mul_right.mul_right).sub (hbc.mul_left.mul_right.mul_right)).mul_left

end
end Yau.Target

end OAI
