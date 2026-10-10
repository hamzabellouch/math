import OAI.Probability.InvariantIsing.Haar.ReflectionSegmentDerivative

namespace OAI

/-! A genuine special-orthogonal curve for a pair of hyperplane reflections. -/
noncomputable section
open Matrix Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def reflectionPair {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) : SpecialOrthogonal N :=
  ⟨rotationMatrix (hyperplaneReflection v)*rotationMatrix (hyperplaneReflection w),
    Matrix.mem_specialOrthogonalGroup_iff.mpr
      ⟨(Matrix.orthogonalGroup (Fin N) ℝ).mul_mem (rotationMatrix_mem _) (rotationMatrix_mem _),
        by rw [Matrix.det_mul,rotationMatrix_reflection_det v hv,
          rotationMatrix_reflection_det w hw]; norm_num⟩⟩

def reflectionPairCurve {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hw : w ≠ 0) (t : ℝ) : SpecialOrthogonal N :=
  if h : reflectionNormalSegment v w t ≠ 0 then
    reflectionPair (reflectionNormalSegment v w t) w h hw else 1

lemma reflectionPairCurve_hasDerivAt {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hw : w ≠ 0) (t : ℝ) (ht : reflectionNormalSegment v w t ≠ 0) (i j : Fin N) :
    HasDerivAt (fun s => (reflectionPairCurve v w hw s : Matrix (Fin N) (Fin N) ℝ) i j)
      ((reflectionSegmentDerivative v w t*rotationMatrix (hyperplaneReflection w)) i j) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (reflectionSegmentMatrix_hasDerivAt v w t ht i k).mul_const
      (rotationMatrix (hyperplaneReflection w) k j)
  have hn : ∀ᶠ s in 𝓝 t, reflectionNormalSegment v w s ≠ 0 := by
    have hc : Continuous (reflectionNormalSegment v w) := by
      unfold reflectionNormalSegment
      fun_prop
    exact hc.continuousAt.eventually_ne ht
  have he : (fun s => (reflectionPairCurve v w hw s : Matrix (Fin N) (Fin N) ℝ) i j) =ᶠ[𝓝 t]
      fun s => ∑ k, reflectionSegmentMatrix v w s i k*rotationMatrix (hyperplaneReflection w) k j := by
    filter_upwards [hn] with s hs
    simp only [reflectionPairCurve,dite_eq_left hs,reflectionPair,Matrix.mul_apply,reflectionSegmentMatrix]
  exact hd.congr_of_eventuallyEq he

lemma reflectionPairCurve_zero {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) : reflectionPairCurve v w hw 0 = reflectionPair v w hv hw := by
  simp only [reflectionPairCurve,reflectionNormalSegment,sub_zero,one_smul,zero_smul,add_zero,
    dite_eq_left hv]

lemma reflectionPairCurve_one {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hw : w ≠ 0) : reflectionPairCurve v w hw 1 = 1 := by
  apply Subtype.ext
  simp only [reflectionPairCurve,reflectionNormalSegment,sub_self,zero_smul,one_smul,zero_add,
    dite_eq_left hw,reflectionPair]
  rw [← rotationMatrix_mul,show hyperplaneReflection w*hyperplaneReflection w = 1 from
    Submodule.reflection_mul_reflection _,rotationMatrix_one]
  rfl

end InvariantIsing

end

end OAI
