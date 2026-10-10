import OAI.Probability.SLE.Gauge.CoverEvents

namespace OAI

/-! A finite physical grid in a bounded disk, with the planar cell count
needed by the missed-cell estimate. Closed disks are used as fine cells. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

def coverGridCenter (r : ℝ) (ij : ℤ × ℤ) : ℂ :=
  (r * (ij.1 : ℝ) : ℝ) + (r * (ij.2 : ℝ) : ℝ) * Complex.I

def coverGridIndex (R r : ℝ) : Finset (ℤ × ℤ) :=
  let N : ℤ := ⌈R / r⌉ + 1
  (Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N)

def retainedCoverGridIndex (R r : ℝ) (K : Set ℂ) : Finset (ℤ × ℤ) := by
  classical
  exact (coverGridIndex R r).filter (fun ij =>
    (K ∩ closedBall (coverGridCenter r ij) (2 * r)).Nonempty)

lemma coverGrid_coordinate {R r x : ℝ} (_hR : 0 ≤ R) (hr : 0 < r)
    (hx : |x| ≤ R) :
    -(⌈R / r⌉ + 1) ≤ ⌊x / r⌋ ∧ ⌊x / r⌋ ≤ ⌈R / r⌉ + 1 := by
  have hl := Int.sub_one_lt_floor (x / r)
  have hu := Int.floor_le (x / r)
  have hc := Int.le_ceil (R / r)
  have hxl : -R / r ≤ x / r := div_le_div_of_nonneg_right (abs_le.mp hx).1 hr.le
  have hxl' : -(R / r) ≤ x / r := by simpa only [neg_div] using hxl
  have hxu : x / r ≤ R / r := div_le_div_of_nonneg_right (abs_le.mp hx).2 hr.le
  have hlow : ((-(⌈R / r⌉ + 1) : ℤ) : ℝ) ≤ (⌊x / r⌋ : ℝ) := by
    push_cast
    linarith
  have hhigh : (⌊x / r⌋ : ℝ) ≤ ((⌈R / r⌉ + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  exact ⟨by exact_mod_cast hlow, by exact_mod_cast hhigh⟩

lemma coverGrid_floor_distance {r : ℝ} (hr : 0 < r) (z : ℂ) :
    dist z (coverGridCenter r (⌊z.re / r⌋, ⌊z.im / r⌋)) ≤ 2 * r := by
  have hre0 : 0 ≤ z.re - r * (⌊z.re / r⌋ : ℝ) := by
    have hh := (Int.floor_le (z.re / r))
    have hm := (mul_le_mul_of_nonneg_left hh hr.le)
    rw [mul_div_cancel₀ _ hr.ne'] at hm
    linarith
  have hre1 : z.re - r * (⌊z.re / r⌋ : ℝ) ≤ r := by
    have hh := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (z.re / r)) hr
    rw [mul_div_cancel₀ _ hr.ne'] at hh
    nlinarith
  have him0 : 0 ≤ z.im - r * (⌊z.im / r⌋ : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (Int.floor_le (z.im / r)) hr.le
    rw [mul_div_cancel₀ _ hr.ne'] at hh
    linarith
  have him1 : z.im - r * (⌊z.im / r⌋ : ℝ) ≤ r := by
    have hh := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (z.im / r)) hr
    rw [mul_div_cancel₀ _ hr.ne'] at hh
    nlinarith
  rw [dist_eq_norm]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [coverGridCenter, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add, abs_of_nonneg hre0, abs_of_nonneg him0]
  linarith

theorem coverGrid_covers_disk {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    closedBall (0 : ℂ) R ⊆
      ⋃ ij ∈ coverGridIndex R r, closedBall (coverGridCenter r ij) (2 * r) := by
  intro z hz
  have hzn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hre := coverGrid_coordinate hR hr ((Complex.abs_re_le_norm z).trans hzn)
  have him := coverGrid_coordinate hR hr ((Complex.abs_im_le_norm z).trans hzn)
  apply mem_iUnion₂.mpr
  refine ⟨(⌊z.re / r⌋, ⌊z.im / r⌋), ?_, coverGrid_floor_distance hr z⟩
  simpa only [coverGridIndex, Finset.mem_product, Finset.mem_Icc] using And.intro hre him

/-- The constant depends on the bounded disk, and not on the small mesh. -/
theorem coverGrid_card_bound {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    ((coverGridIndex R r).card : ℝ) ≤ (2 * R + 5) ^ 2 * r ^ (-2 : ℝ) := by
  let N : ℤ := ⌈R / r⌉ + 1
  have hN : 0 ≤ N := by
    have hh : (0 : ℝ) ≤ (⌈R / r⌉ : ℝ) := (div_nonneg hR hr.le).trans (Int.le_ceil _)
    have hh' : (0 : ℤ) ≤ ⌈R / r⌉ := by exact_mod_cast hh
    dsimp [N]
    omega
  have hcard : ((coverGridIndex R r).card : ℝ) = (2 * (N : ℝ) + 1) ^ 2 := by
    have hh := Int.card_Icc_of_le (a := -N) (b := N) (by omega)
    have hhR : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      have hh' : ((Finset.Icc (-N) N).card : ℝ) = (N : ℝ) + 1 - -(N : ℝ) := by
        exact_mod_cast hh
      linarith
    change (((Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N)).card : ℝ) = _
    rw [Finset.card_product, Nat.cast_mul, hhR]
    ring
  have hNbound : (N : ℝ) ≤ R / r + 2 := by
    have hh := Int.ceil_lt_add_one (R / r)
    dsimp [N]
    push_cast
    linarith
  have hside : 2 * (N : ℝ) + 1 ≤ (2 * R + 5) / r := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_right hNbound hr.le
    rw [add_mul, div_mul_cancel₀ _ hr.ne'] at hh
    nlinarith
  rw [hcard, Real.rpow_neg hr.le, Real.rpow_two]
  calc
    _ ≤ ((2 * R + 5) / r) ^ 2 := pow_le_pow_left₀ (by exact_mod_cast (show (0 : ℤ) ≤ 2 * N + 1 by omega)) hside 2
    _ = _ := by rw [div_pow, div_eq_mul_inv]

theorem retainedCoverGrid_covers {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    {K : Set ℂ} (hK : K ⊆ closedBall 0 R) :
    K ⊆ ⋃ ij ∈ retainedCoverGridIndex R r K,
      closedBall (coverGridCenter r ij) (2 * r) := by
  classical
  intro z hz
  obtain ⟨ij, hij, hzcell⟩ := mem_iUnion₂.mp (coverGrid_covers_disk hR hr (hK hz))
  exact mem_iUnion₂.mpr ⟨ij, Finset.mem_filter.mpr ⟨hij, ⟨z, hz, hzcell⟩⟩, hzcell⟩

theorem retainedCoverGrid_card_bound {R r : ℝ} (hR : 0 ≤ R)
    (hr : 0 < r) (hr1 : r ≤ 1) (K : Set ℂ) :
    ((retainedCoverGridIndex R r K).card : ℝ) ≤ (2 * R + 5) ^ 2 * r ^ (-2 : ℝ) := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (coverGrid_card_bound hR hr hr1)

/-- Retaining only cells meeting the interior cutoff keeps all their centers
away from the real boundary and in one fixed enlarged bounded disk. -/
theorem retainedCoverGrid_center_bounds {R r η : ℝ} {K : Set ℂ}
    (hK : K ⊆ closedBall 0 R) (hheight : ∀ z ∈ K, η ≤ z.im)
    {ij : ℤ × ℤ} (hij : ij ∈ retainedCoverGridIndex R r K) :
    ‖coverGridCenter r ij‖ ≤ R + 2 * r ∧
      η - 2 * r ≤ (coverGridCenter r ij).im := by
  classical
  obtain ⟨z, hzK, hzcell⟩ := (Finset.mem_filter.mp hij).2
  have hdist : dist z (coverGridCenter r ij) ≤ 2 * r := hzcell
  have hzn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hK hzK
  have hnorm : ‖coverGridCenter r ij‖ ≤ ‖z‖ + dist z (coverGridCenter r ij) := by
    have hh := dist_triangle (coverGridCenter r ij) z 0
    simpa only [dist_zero_right, dist_comm (coverGridCenter r ij) z, add_comm] using hh
  have him := (Complex.abs_im_le_norm (z - coverGridCenter r ij)).trans
    (by simpa only [dist_eq_norm] using hdist)
  rw [Complex.sub_im] at him
  constructor
  · linarith
  · have hh := (abs_le.mp him).2
    have hz := hheight z hzK
    linarith

lemma coverGrid_cell_diameter {r : ℝ} (_hr : 0 < r) (ij : ℤ × ℤ) :
    ediam (closedBall (coverGridCenter r ij) (2 * r)) ≤ ENNReal.ofReal (4 * r) := by
  apply ediam_le_of_forall_dist_le
  intro x hx y hy
  have hxy := dist_triangle x (coverGridCenter r ij) y
  have hx' : dist x (coverGridCenter r ij) ≤ 2 * r := hx
  have hy' : dist (coverGridCenter r ij) y ≤ 2 * r := by
    have hh : dist y (coverGridCenter r ij) ≤ 2 * r := hy
    simpa only [dist_comm] using hh
  linarith

end SLEExactGauge

end

end OAI
