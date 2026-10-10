import Mathlib
import OAI.Geometry.CAT0Fillings.Scaling.Metric

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
universe u
private noncomputable def cutoffRatio (R r : ℝ) : ℝ := if r ≤ R then 1 else R / r

private lemma cutoffRatio_mem {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) :
    cutoffRatio R r ∈ Icc (0 : ℝ) 1 := by
  unfold cutoffRatio
  split_ifs with h
  · norm_num
  · have hr' : 0 < r := lt_of_le_of_lt hR (lt_of_not_ge h)
    exact ⟨div_nonneg hR hr, (div_le_one hr').mpr (le_of_lt (lt_of_not_ge h))⟩

private lemma cutoffRatio_mul {R r : ℝ} (hR : 0 ≤ R) :
    cutoffRatio R r * r = min r R := by
  unfold cutoffRatio
  split_ifs with h
  · simp [min_eq_left h]
  · have hr' : 0 < r := lt_of_le_of_lt hR (lt_of_not_ge h)
    simp [div_mul_cancel₀ _ hr'.ne', min_eq_right (le_of_lt (lt_of_not_ge h))]

theorem IsCAT0.exists_ball_retraction {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) :
    ∃ P : X → X, LipschitzWith 1 P ∧
      (∀ x, dist o (P x) ≤ R) ∧ (∀ x, dist o x ≤ R → P x = x) := by
  obtain ⟨s, hs, hd, hc⟩ := hX
  let q : X → ℝ := fun x => cutoffRatio R (dist o x)
  have hq (x : X) : q x ∈ Icc (0 : ℝ) 1 := cutoffRatio_mem hR dist_nonneg
  have hm (x : X) : q x * dist o x = min (dist o x) R :=
    cutoffRatio_mul hR
  let P : X → X := fun x => s o x (q x)
  refine ⟨P, ?_, ?_, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    have hh := hc o x y (q x) (q y) (hq x) (hq y)
    rw [hm x, hm y] at hh
    have hc₀ : 0 ≤ dist x y ^ 2 - (dist o x - dist o y) ^ 2 := by
      have hh' := abs_dist_sub_le x y o
      rw [dist_comm x o, dist_comm y o] at hh'
      have hh'' := (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mpr hh'
      rw [sq_abs] at hh''
      linarith
    have hqq : q x * q y ≤ 1 := by
      nlinarith [(hq x).1, (hq y).1, (hq x).2, (hq y).2,
        mul_nonneg (sub_nonneg.mpr (hq x).2) (sub_nonneg.mpr (hq y).2)]
    have hmin := (LipschitzWith.id.min_const R).dist_le_mul (dist o x) (dist o y)
    simp only [id_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hmin
    have hmin' := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hmin
    simp only [sq_abs] at hmin'
    have hmul := mul_le_mul_of_nonneg_right hqq hc₀
    have hsq : dist (P x) (P y) ^ 2 ≤ dist x y ^ 2 := by
      change dist (s o x (q x)) (s o y (q y)) ^ 2 ≤ _
      nlinarith
    simpa using (sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq
  · intro x
    have hh := hd o x 0 (q x) (by simp) (hq x)
    rw [(hs o x).1] at hh
    simp only [zero_sub, abs_neg, abs_of_nonneg (hq x).1] at hh
    change dist o (s o x (q x)) ≤ R
    rw [hh, hm x]
    exact min_le_right _ _
  · intro x hx
    change s o x (cutoffRatio R (dist o x)) = x
    simp only [cutoffRatio, ite_eq_left hx]
    exact (hs o x).2

theorem IsCAT0.closedBall {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) : IsCAT0 (Metric.closedBall o R) := by
  obtain ⟨s, hs, hd, hc⟩ := hX
  have hconv (x y : Metric.closedBall o R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      s x.val y.val t ∈ Metric.closedBall o R := by
    have hh := hc x.val y.val o t 1 ht (by simp)
    rw [(hs x.val o).2] at hh
    have he : (t * dist x.val y.val - 1 * dist x.val o) ^ 2 +
          t * 1 * (dist y.val o ^ 2 - (dist x.val y.val - dist x.val o) ^ 2) =
        (1 - t) * dist x.val o ^ 2 + t * dist y.val o ^ 2 -
          t * (1 - t) * dist x.val y.val ^ 2 := by ring
    rw [he] at hh
    have hx := (sq_le_sq₀ dist_nonneg hR).mpr x.property
    have hy := (sq_le_sq₀ dist_nonneg hR).mpr y.property
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)
    have hy' := mul_le_mul_of_nonneg_left hy ht.1
    have hh' : dist (s x.val y.val t) o ^ 2 ≤ R ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
        (sq_nonneg (dist x.val y.val))]
    exact (sq_le_sq₀ dist_nonneg hR).mp hh'
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclamp_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
    simp only [clamp, min_eq_right ht.2, max_eq_right ht.1]
  let sB : Metric.closedBall o R → Metric.closedBall o R → ℝ →
      Metric.closedBall o R := fun x y t => ⟨s x.val y.val (clamp t), hconv x y _ (hclamp t)⟩
  refine ⟨sB, ?_, ?_, ?_⟩
  · intro x y
    constructor <;> apply Subtype.ext
    · change s x.val y.val (clamp 0) = x.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).1]
    · change s x.val y.val (clamp 1) = y.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).2]
  · intro x y u v hu hv
    change dist (s x.val y.val (clamp u)) (s x.val y.val (clamp v)) = _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hd x.val y.val u v hu hv
  · intro p x y u v hu hv
    change dist (s p.val x.val (clamp u)) (s p.val y.val (clamp v)) ^ 2 ≤ _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hc p.val x.val y.val u v hu hv

end CAT0Fillings
end

end OAI
