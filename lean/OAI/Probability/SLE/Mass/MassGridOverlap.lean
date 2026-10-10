import OAI.Probability.SLE.Gauge.CoverGrid

namespace OAI

/-! A fixed overlap bound for planar mass cutoffs on the physical grid. -/

noncomputable section
open Set Metric Filter MeasureTheory Classical
open scoped ENNReal

namespace SLEExactGauge

lemma massGrid_coordinate_bounds {r x : ℝ} (hr : 0 < r) (i : ℤ)
    (hi : |x-r*(i:ℝ)| ≤ 3*r) :
    ⌊x/r⌋-4 ≤ i ∧ i ≤ ⌊x/r⌋+4 := by
  have hf : r*(⌊x/r⌋:ℝ) ≤ x := by
    have hh := mul_le_mul_of_nonneg_left (Int.floor_le (x/r)) hr.le
    rwa [mul_div_cancel₀ _ hr.ne'] at hh
  have hg : x < r*((⌊x/r⌋:ℝ)+1) := by
    have hh := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x/r)) hr
    rwa [mul_div_cancel₀ _ hr.ne'] at hh
  have hlo : ((⌊x/r⌋-4:ℤ):ℝ) ≤ (i:ℝ) := by
    push_cast
    nlinarith [abs_le.mp hi]
  have hhi : (i:ℝ) ≤ ((⌊x/r⌋+4:ℤ):ℝ) := by
    push_cast
    nlinarith [abs_le.mp hi]
  exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩

lemma massGrid_nearby_card_le {r : ℝ} (hr : 0 < r) (I : Finset (ℤ×ℤ)) (z : ℂ) :
    (I.filter (fun ij => dist z (coverGridCenter r ij) ≤ 3*r)).card ≤ 81 := by
  let J := (Finset.Icc (⌊z.re/r⌋-4) (⌊z.re/r⌋+4)) ×ˢ
    (Finset.Icc (⌊z.im/r⌋-4) (⌊z.im/r⌋+4))
  have hsub : I.filter (fun ij => dist z (coverGridCenter r ij) ≤ 3*r) ⊆ J := by
    intro ij hij
    have hd := (Finset.mem_filter.mp hij).2
    have hre : |z.re-r*(ij.1:ℝ)| ≤ 3*r := by
      have h := (Complex.abs_re_le_norm (z-coverGridCenter r ij)).trans
        (by simpa only [dist_eq_norm] using hd)
      simpa [coverGridCenter] using h
    have him : |z.im-r*(ij.2:ℝ)| ≤ 3*r := by
      have h := (Complex.abs_im_le_norm (z-coverGridCenter r ij)).trans
        (by simpa only [dist_eq_norm] using hd)
      simpa [coverGridCenter] using h
    simpa only [J,Finset.mem_product,Finset.mem_Icc] using
      And.intro (massGrid_coordinate_bounds hr ij.1 hre) (massGrid_coordinate_bounds hr ij.2 him)
  have hcard : J.card = 81 := by
    simp only [J,Finset.card_product,Int.card_Icc]
    rw [show ⌊z.re/r⌋+4+1-(⌊z.re/r⌋-4) = (9:ℤ) by omega,
      show ⌊z.im/r⌋+4+1-(⌊z.im/r⌋-4) = (9:ℤ) by omega]
    rfl
  exact (Finset.card_le_card hsub).trans_eq hcard

lemma massGrid_cutoff_product_sum_le {r : ℝ} (hr : 0 < r) (I : Finset (ℤ×ℤ))
    (f : (ℤ×ℤ) → ℂ → ℝ≥0∞) (hf : ∀ i z, f i z ≤ 1)
    (hs : ∀ i z, f i z ≠ 0 → dist z (coverGridCenter r i) ≤ 3*r)
    (x y : ℂ) :
    (∑ i ∈ I, f i x * f i y) ≤ if dist x y ≤ 6*r then 81 else 0 := by
  by_cases hxy : dist x y ≤ 6*r
  · rw [ite_eq_left hxy]
    let J := I.filter (fun i => dist x (coverGridCenter r i) ≤ 3*r)
    have he : (∑ i ∈ I, f i x * f i y) = ∑ i ∈ J, f i x * f i y := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hij
      have hx : f i x = 0 := by
        by_contra h
        exact hij (Finset.mem_filter.mpr ⟨hi,hs i x h⟩)
      simp only [hx,zero_mul]
    rw [he]
    calc
      _ ≤ ∑ _i ∈ J, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun i _ => (mul_le_mul' (hf i x) (hf i y)).trans_eq (one_mul 1))
      _ = J.card := by simp
      _ ≤ 81 := by exact_mod_cast massGrid_nearby_card_le hr I x
  · rw [ite_eq_right hxy]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hx : f i x = 0
    · simp only [hx,zero_mul]
    by_cases hy : f i y = 0
    · simp only [hy,mul_zero]
    exact False.elim (hxy ((dist_triangle_right x y (coverGridCenter r i)).trans
      (by linarith [hs i x hx,hs i y hy])))

end SLEExactGauge

end

end OAI
