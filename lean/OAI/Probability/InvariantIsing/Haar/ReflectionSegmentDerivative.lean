import OAI.Probability.InvariantIsing.Haar.ReflectionSegment

namespace OAI

/-! Entry derivatives along a nonsingular interpolation of reflection normals. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

def reflectionSegmentMatrix {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  rotationMatrix (hyperplaneReflection (reflectionNormalSegment v w t))

def reflectionSegmentDerivative {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j =>
  -((2*((w i-v i)*reflectionNormalSegment v w t j+
      reflectionNormalSegment v w t i*(w j-v j)))*reflectionNormalSquare v w t-
      (2*reflectionNormalSegment v w t i*reflectionNormalSegment v w t j)*
        reflectionNormalSquareDeriv v w t)/(reflectionNormalSquare v w t)^2

lemma reflectionSegmentMatrix_hasDerivAt {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ)
    (ht : reflectionNormalSegment v w t ≠ 0) (i j : Fin N) :
    HasDerivAt (fun s => reflectionSegmentMatrix v w s i j)
      (reflectionSegmentDerivative v w t i j) t := by
  have hq : reflectionNormalSquare v w t ≠ 0 := by
    rw [reflectionNormalSquare_eq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr ht)
  have hd := (hasDerivAt_const t ((1 : Matrix (Fin N) (Fin N) ℝ) i j)).sub
    ((((reflectionNormalSegment_hasDerivAt v w t i).const_mul 2).mul
      (reflectionNormalSegment_hasDerivAt v w t j)).div
      (reflectionNormalSquare_hasDerivAt v w t) hq)
  convert hd using 1
  · funext s
    change rotationMatrix (hyperplaneReflection (reflectionNormalSegment v w s)) i j =
      (1 : Matrix (Fin N) (Fin N) ℝ) i j-
        2*reflectionNormalSegment v w s i*reflectionNormalSegment v w s j /
          reflectionNormalSquare v w s
    rw [reflectionNormalSquare_eq,rotationMatrix_reflection_apply]
  · dsimp only [reflectionSegmentDerivative,Matrix.of_apply]
    simp only [Pi.mul_apply]
    ring

lemma continuousOn_reflectionSegmentDerivative {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : 0 ≤ inner ℝ v w) (i j : Fin N) :
    ContinuousOn (fun t => reflectionSegmentDerivative v w t i j) (Icc (0:ℝ) 1) := by
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : reflectionNormalSquare v w t ≠ 0 := by
    rw [reflectionNormalSquare_eq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr
      (reflectionNormalSegment_nonzero v w hv hw hvw ht))
  have hn (k : Fin N) : ContinuousOn (fun t => reflectionNormalSegment v w t k)
      (Icc (0:ℝ) 1) := (continuous_reflectionNormalSegment_entry v w k).continuousOn
  have hs : ContinuousOn (reflectionNormalSquare v w) (Icc (0:ℝ) 1) :=
    (continuous_reflectionNormalSquare v w).continuousOn
  have hd : ContinuousOn (reflectionNormalSquareDeriv v w) (Icc (0:ℝ) 1) :=
    (continuous_reflectionNormalSquareDeriv v w).continuousOn
  dsimp only [reflectionSegmentDerivative,Matrix.of_apply]
  exact ((((continuousOn_const.mul
    ((continuousOn_const.mul (hn j)).add ((hn i).mul continuousOn_const))).mul hs).sub
      (((continuousOn_const.mul (hn i)).mul (hn j)).mul hd)).neg).div (hs.pow 2)
        (fun t ht => pow_ne_zero _ (hq t ht))

end InvariantIsing

end

end OAI
