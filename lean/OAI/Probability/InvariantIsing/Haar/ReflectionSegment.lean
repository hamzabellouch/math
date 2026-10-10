import OAI.Probability.InvariantIsing.Haar.RotationMatrix
import OAI.Probability.InvariantIsing.Haar.HaarCurveBound

namespace OAI

/-! Nonsingular interpolation of reflection normals. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

def reflectionNormalSegment {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    EuclideanSpace ℝ (Fin N) := (1-t) • v+t • w

lemma reflectionNormalSegment_nonzero {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : 0 ≤ inner ℝ v w)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : reflectionNormalSegment v w t ≠ 0 := by
  by_cases h1 : t = 1
  · simpa [reflectionNormalSegment,h1] using hw
  have hinner : 0 < inner ℝ v (reflectionNormalSegment v w t) := by
    simp only [reflectionNormalSegment,inner_add_right,inner_smul_right,
      real_inner_self_eq_norm_sq]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 h1)) (sq_pos_of_pos (norm_pos_iff.mpr hv)))
      (mul_nonneg ht.1 hvw)
  intro hz
  rw [hz,inner_zero_right] at hinner
  exact lt_irrefl _ hinner

lemma reflectionNormalSegment_hasDerivAt {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) (i : Fin N) :
    HasDerivAt (fun s => reflectionNormalSegment v w s i) (w i-v i) t := by
  have h := (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const (v i)).add
    ((hasDerivAt_id t).mul_const (w i))
  convert h using 1
  · rfl
  · simp only [zero_sub,one_mul,neg_mul]
    ring

def reflectionNormalSquare {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) : ℝ :=
  ∑ i, (reflectionNormalSegment v w t i)^2

def reflectionNormalSquareDeriv {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) : ℝ :=
  ∑ i, 2*reflectionNormalSegment v w t i*(w i-v i)

lemma reflectionNormalSquare_eq {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    reflectionNormalSquare v w t = ‖reflectionNormalSegment v w t‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma reflectionNormalSquare_hasDerivAt {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    HasDerivAt (reflectionNormalSquare v w) (reflectionNormalSquareDeriv v w t) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (reflectionNormalSegment_hasDerivAt v w t i).pow 2
  convert hd using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.cast_ofNat]
    ring

lemma continuous_reflectionNormalSegment_entry {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Continuous (fun t => reflectionNormalSegment v w t i) := by
  change Continuous (fun t : ℝ => (1-t)*v i+t*w i)
  fun_prop

lemma continuous_reflectionNormalSquare {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) :
    Continuous (reflectionNormalSquare v w) := by
  unfold reflectionNormalSquare
  exact continuous_finsetSum _ fun i _ => (continuous_reflectionNormalSegment_entry v w i).pow 2

lemma continuous_reflectionNormalSquareDeriv {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) :
    Continuous (reflectionNormalSquareDeriv v w) := by
  unfold reflectionNormalSquareDeriv
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_reflectionNormalSegment_entry v w i)).mul continuous_const

end InvariantIsing

end

end OAI
