import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.HalfheightFinite

lemma profile_nonnegative (r : ℝ) : 0 ≤ profile r := by
  unfold profile
  positivity

lemma cubicCap_continuous (δ : ℝ) : Continuous (cubicCap δ) := by
  unfold cubicCap profile
  fun_prop

lemma fractionalCap_continuous (δ : ℝ) : Continuous (fractionalCap δ) := by
  unfold fractionalCap profile
  fun_prop

lemma cubicCap_positive {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) :
    0 < cubicCap δ r := by
  unfold cubicCap
  have hp := profile_nonnegative r
  positivity

lemma fractionalCap_positive {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) :
    0 < fractionalCap δ r := by
  unfold fractionalCap
  have hp := profile_nonnegative r
  positivity

end CylinderCovering.HalfheightFinite

end

end OAI
