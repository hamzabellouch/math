import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SignedVertex

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

noncomputable def maxIndex {m : ℕ} [NeZero m] (g : Fin m → ℝ) : Fin m :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose

lemma maxIndex_le {m : ℕ} [NeZero m] (g : Fin m → ℝ) (i : Fin m) :
    g i ≤ g (maxIndex g) :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ _)

noncomputable def peakIndex {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) : Fin m :=
  maxIndex (fun i => |y i|)

lemma peakIndex_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    peakIndex (-y) = peakIndex y := by
  unfold peakIndex
  congr 1
  ext i
  simp

lemma euclidean_norm_le_sum_abs {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖y‖ ≤ ∑ i, |y i| := by
  have hy : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext i
    simp
  calc
    ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := congrArg norm hy
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| := by simp

lemma peak_large {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    (1:ℝ) / m ≤ |y (peakIndex y)| := by
  have h := euclidean_norm_le_sum_abs y
  rw [hy] at h
  have hsum : ∑ i : Fin m, |y i| ≤ (m:ℝ) * |y (peakIndex y)| := by
    calc
      ∑ i : Fin m, |y i| ≤ ∑ _ : Fin m, |y (peakIndex y)| :=
        Finset.sum_le_sum (fun i _ => maxIndex_le (fun j => |y j|) i)
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)

noncomputable def sphereLabel {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) : SignedVertex :=
  ((peakIndex y).val, decide (y (peakIndex y) < 0))

lemma sphereLabel_bound {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    (sphereLabel y).1 < m := (peakIndex y).isLt

lemma sphereLabel_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    sphereLabel (-y) = flip (sphereLabel y) := by
  have hpeak : y (peakIndex y) ≠ 0 := by
    have h := peak_large y hy
    have hm : (0:ℝ) < (1:ℝ)/m := div_pos zero_lt_one (by exact_mod_cast NeZero.pos m)
    intro he
    rw [he, abs_zero] at h
    linarith
  apply Prod.ext
  · simp only [sphereLabel, peakIndex_neg, flip_apply]
  · simp only [sphereLabel, peakIndex_neg, flip_apply, PiLp.neg_apply]
    by_cases h : y (peakIndex y) < 0
    · have h' : ¬ -y (peakIndex y) < 0 := by linarith
      simp [h,h']
    · have h' : -y (peakIndex y) < 0 := by rcases lt_or_gt_of_ne hpeak with hn | hp <;> linarith
      simp [h,h']

lemma sphereLabel_compatible {m : ℕ} [NeZero m]
    (y z : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hd : dist y z < (1:ℝ)/m) (hi : (sphereLabel y).1 = (sphereLabel z).1) :
    sphereLabel y = sphereLabel z := by
  have he : peakIndex y = peakIndex z := Fin.ext hi
  have hcoord : |y (peakIndex y) - z (peakIndex y)| ≤ dist y z := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y z (peakIndex y)
  have hym := peak_large y hy
  have hzm := peak_large z hz
  rw [← he] at hzm
  apply Prod.ext hi
  change decide (y (peakIndex y) < 0) = decide (z (peakIndex z) < 0)
  rw [← he]
  congr 1
  apply propext
  constructor
  · intro hyneg
    by_contra hzneg
    have hzpos := le_of_not_gt hzneg
    rw [abs_of_neg hyneg] at hym
    rw [abs_of_nonpos (by linarith)] at hcoord
    linarith
  · intro hzneg
    by_contra hyneg
    have hypos := le_of_not_gt hyneg
    rw [abs_of_neg hzneg] at hzm
    rw [abs_of_nonneg (by linarith)] at hcoord
    linarith

end BorsukNine.SimplicialChains

end OAI
