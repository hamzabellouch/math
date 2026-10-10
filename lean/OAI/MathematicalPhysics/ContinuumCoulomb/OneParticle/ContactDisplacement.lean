import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactAdjustment

namespace OAI

/-! Uniform displacement bounds for the explicit independent-length paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem adjustedContactForward_antitone {length h h' : ℝ} (hh : 0 ≤ h) (hle : h ≤ h') :
    adjustedContactForward length h' ≤ adjustedContactForward length h := by
  apply Real.sqrt_le_sqrt
  nlinarith

theorem adjustedContactForward_near {c h length : ℝ}
    (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (hl : 1 - contactLengthTolerance ≤ length) (hl' : length ≤ 1 + contactLengthTolerance) :
    |adjustedContactForward length h - c| ≤ 11 / 10000 := by
  have hlow := adjustedContactForward_bound hl hl'
    (show 7 / 10 ≤ c + 1 / 1000 by linarith)
    (show c + 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightLow_sq hc hc')
  have hhigh := adjustedContactForward_bound hl hl'
    (show 7 / 10 ≤ c - 1 / 1000 by linarith)
    (show c - 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightHigh_sq hc hc')
  have hlo : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hh0 : 0 ≤ h := hlo.trans hh.1
  have ha := adjustedContactForward_antitone (length := length) hlo hh.1
  have hb := adjustedContactForward_antitone (length := length) hh0 hh.2
  apply abs_le.mpr
  constructor <;> linarith

theorem contactHeight_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) :
    |h - contactSlopeHeight c| ≤ 1 / 250 := by
  have hbase := contactSlopeHeight_sq (by linarith : -1 ≤ c) (by linarith : c ≤ 1)
  have hlowsq := contactHeightLow_sq hc hc'
  have hhighsq := contactHeightHigh_sq hc hc'
  have hbase0 : 0 ≤ contactSlopeHeight c := Real.sqrt_nonneg _
  have hlow0 : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hhigh0 : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  have hbaseMin : 2 / 5 ≤ contactSlopeHeight c := by nlinarith
  have hlowMin : 2 / 5 ≤ contactHeightLow c := by nlinarith
  have hhighMin : 2 / 5 ≤ contactHeightHigh c := by nlinarith
  have hlowNear : contactSlopeHeight c - 1 / 250 ≤ contactHeightLow c := by nlinarith
  have hhighNear : contactHeightHigh c ≤ contactSlopeHeight c + 1 / 250 := by nlinarith
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem adjustedContactStepX_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k < 9) :
    |adjustedContactStepX lengths h k - contactStepX c k| ≤ 11 / 10000 := by
  unfold adjustedContactStepX contactStepX
  split_ifs
  · exact adjustedContactForward_near hc hc' hh (hl k hk) (hl' k hk)
  · apply abs_le.mpr
    have h1 := hl k hk
    have h2 := hl' k hk
    unfold contactLengthTolerance at h1 h2
    constructor <;> linarith

theorem adjustedContactStepY_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) (k : ℕ) :
    |adjustedContactStepY h k - contactStepY c k| ≤ 1 / 250 := by
  have hnear := contactHeight_near hc hc' hh
  unfold adjustedContactStepY contactStepY
  split_ifs
  · exact hnear
  · simpa only [neg_sub_neg, abs_sub_comm] using hnear
  · norm_num

theorem contact_sum_error {f g : ℕ → ℝ} {k : ℕ} {eta : ℝ}
    (h : ∀ j < k, |f j - g j| ≤ eta) :
    |(∑ j ∈ Finset.range k, f j) - ∑ j ∈ Finset.range k, g j| ≤ k * eta := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range k, |f j - g j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, eta := Finset.sum_le_sum (fun j hj => h j (Finset.mem_range.mp hj))
    _ = _ := by simp

/-- A uniform displacement bound with room for moving the path origin. -/
theorem adjustedContactVertex_displacement {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ j < 9, 1 - contactLengthTolerance ≤ lengths j)
    (hl' : ∀ j < 9, lengths j ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k ≤ 9) :
    dist (adjustedContactVertex lengths h k) (contactPathVertex c k) < 1 / 25 := by
  have hx := contact_sum_error (k := k)
    (fun j hj => adjustedContactStepX_near hc hc' hh lengths hl hl' (by omega : j < 9))
  have hy := contact_sum_error (k := k)
    (fun j _ => adjustedContactStepY_near hc hc' hh j)
  have hkreal : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hx' : |adjustedContactVertex lengths h k 0 - contactPathVertex c k 0| ≤ 99 / 10000 := by
    change |(∑ j ∈ Finset.range k, adjustedContactStepX lengths h j) -
      ∑ j ∈ Finset.range k, contactStepX c j| ≤ 99 / 10000
    linarith
  have hy' : |adjustedContactVertex lengths h k 1 - contactPathVertex c k 1| ≤ 9 / 250 := by
    change |(∑ j ∈ Finset.range k, adjustedContactStepY h j) -
      ∑ j ∈ Finset.range k, contactStepY c j| ≤ 9 / 250
    linarith
  have hdist := contactPoint_dist_sq
    (∑ j ∈ Finset.range k, adjustedContactStepX lengths h j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h j)
    (∑ j ∈ Finset.range k, contactStepX c j)
    (∑ j ∈ Finset.range k, contactStepY c j)
  change dist (adjustedContactVertex lengths h k) (contactPathVertex c k) ^ 2 =
    (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0) ^ 2 +
    (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1) ^ 2 at hdist
  have hxSq : (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0) ^ 2 ≤ (99 / 10000 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg
      (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0))
      (by norm_num : (0 : ℝ) ≤ 99 / 10000)).mpr hx'
  have hySq : (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1) ^ 2 ≤ (9 / 250 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg
      (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1))
      (by norm_num : (0 : ℝ) ≤ 9 / 250)).mpr hy'
  nlinarith [show 0 ≤ dist (adjustedContactVertex lengths h k) (contactPathVertex c k) from dist_nonneg]

theorem adjustedContactVertex_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ j < 9, 1 - contactLengthTolerance ≤ lengths j)
    (hl' : ∀ j < 9, lengths j ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k ≤ 9) :
    dist (adjustedContactVertex lengths h k) (contactPathVertex c k) < 1 / 20 :=
  (adjustedContactVertex_displacement hc hc' hh lengths hl hl' hk).trans (by norm_num)

end ContinuumCoulomb

end

end OAI
