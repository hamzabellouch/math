import OAI.Probability.InvariantIsing.Haar.ReflectionPairCurve
import OAI.Probability.InvariantIsing.Haar.HaarDifferentiableCurve

namespace OAI

/-! Every nonzero reflection pair admits a differentiable curve to the identity. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma hyperplaneReflection_neg {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) :
    hyperplaneReflection (-v) = hyperplaneReflection v := by
  have hs : (ℝ ∙ (-v)) = (ℝ ∙ v) := by
    simpa only [Set.neg_singleton] using (Submodule.span_neg (R := ℝ) ({v} : Set _))
  unfold hyperplaneReflection
  simp only [hs]

def reflectionPairPath {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : 0 ≤ inner ℝ v w) : HaarDifferentiableCurve N where
  value := reflectionPairCurve v w hw
  velocity := fun t => reflectionSegmentDerivative v w t*rotationMatrix (hyperplaneReflection w)
  hasDeriv := fun t ht i j => reflectionPairCurve_hasDerivAt v w hw t
    (reflectionNormalSegment_nonzero v w hv hw hvw ht) i j
  continuous_velocity := by
    intro i j
    simp only [Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun k _ =>
      (continuousOn_reflectionSegmentDerivative v w hv hw hvw i k).mul continuousOn_const

lemma reflectionPair_exists_path {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ γ : HaarDifferentiableCurve N,
      γ.value 0 = reflectionPair v w hv hw ∧ γ.value 1 = 1 := by
  by_cases h : 0 ≤ inner ℝ v w
  · exact ⟨reflectionPairPath v w hv hw h,reflectionPairCurve_zero v w hv hw,
      reflectionPairCurve_one v w hw⟩
  · have hw' : -w ≠ 0 := neg_ne_zero.mpr hw
    have h' : 0 ≤ inner ℝ v (-w) := by rw [inner_neg_right]; linarith
    refine ⟨reflectionPairPath v (-w) hv hw' h',?_,reflectionPairCurve_one v (-w) hw'⟩
    change reflectionPairCurve v (-w) hw' 0 = _
    rw [reflectionPairCurve_zero v (-w) hv hw']
    apply Subtype.ext
    change rotationMatrix (hyperplaneReflection v)*rotationMatrix (hyperplaneReflection (-w)) = _
    rw [hyperplaneReflection_neg]
    rfl

end InvariantIsing

end

end OAI
