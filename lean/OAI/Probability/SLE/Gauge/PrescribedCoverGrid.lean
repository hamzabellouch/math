import OAI.Probability.SLE.Gauge.CoverGrid

namespace OAI

/-! The final mesh is shifted by half a row. Every retained center is in
the open half-plane, while its closed cell can cover the real boundary. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def prescribedGridCenter (r : ℝ) (ij : ℤ × ℤ) : ℂ :=
  coverGridCenter r ij + (r/2:ℝ)*Complex.I

def prescribedFineCell (r : ℝ) (ij : ℤ × ℤ) : Set ℂ :=
  closedBall (prescribedGridCenter r ij) (3*r)

def prescribedGridIndex (R r : ℝ) (K : Set ℂ) : Finset (ℤ × ℤ) := by
  classical
  exact (coverGridIndex R r).filter (fun ij =>
    0 ≤ ij.2 ∧ (K ∩ prescribedFineCell r ij).Nonempty)

lemma prescribedGrid_floor_distance {r : ℝ} (hr : 0<r) (z : ℂ) :
    dist z (prescribedGridCenter r (⌊z.re/r⌋,⌊z.im/r⌋))  ≤  3*r := by
  apply (dist_triangle z (coverGridCenter r (⌊z.re/r⌋,⌊z.im/r⌋)) _).trans
  have hdist : dist (coverGridCenter r (⌊z.re/r⌋,⌊z.im/r⌋))
      (prescribedGridCenter r (⌊z.re/r⌋,⌊z.im/r⌋)) = r/2 := by
    rw [prescribedGridCenter,dist_self_add_right,norm_mul,Complex.norm_real,
      Complex.norm_I,mul_one,Real.norm_eq_abs,abs_of_pos (by positivity)]
  rw [hdist]
  linarith [coverGrid_floor_distance hr z]

lemma prescribedGrid_covers {R r : ℝ} (hR : 0 ≤ R) (hr : 0<r)
    {K : Set ℂ} (hK : K ⊆ closedBall 0 R) (hH : ∀ z∈K, 0 ≤ z.im) :
    K ⊆ ⋃ ij∈prescribedGridIndex R r K, prescribedFineCell r ij := by
  classical
  intro z hz
  let ij : ℤ × ℤ := (⌊z.re/r⌋,⌊z.im/r⌋)
  have hnorm : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hK hz
  have hre := coverGrid_coordinate hR hr ((Complex.abs_re_le_norm z).trans hnorm)
  have him := coverGrid_coordinate hR hr ((Complex.abs_im_le_norm z).trans hnorm)
  have hmem : ij∈coverGridIndex R r := by
    simpa only [ij,coverGridIndex,Finset.mem_product,Finset.mem_Icc] using And.intro hre him
  have hrow : 0 ≤ ij.2 := Int.floor_nonneg.mpr (div_nonneg (hH z hz) hr.le)
  have hcell : z∈prescribedFineCell r ij := prescribedGrid_floor_distance hr z
  exact mem_iUnion₂.mpr ⟨ij,Finset.mem_filter.mpr ⟨hmem,hrow,⟨z,hz,hcell⟩⟩,hcell⟩

lemma prescribedGrid_center_height {R r : ℝ} (hr : 0<r) {K : Set ℂ}
    {ij : ℤ × ℤ} (hij : ij∈prescribedGridIndex R r K) :
    (prescribedGridCenter r ij).im = ((ij.2:ℝ)+1/2)*r ∧
      0<(prescribedGridCenter r ij).im := by
  classical
  have hrow : (0:ℝ) ≤ ij.2 := by exact_mod_cast (Finset.mem_filter.mp hij).2.1
  have he : (prescribedGridCenter r ij).im = ((ij.2:ℝ)+1/2)*r := by
    simp only [prescribedGridCenter,coverGridCenter,Complex.add_im,Complex.ofReal_im,
      Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
      add_zero,zero_add]
    ring
  exact ⟨he,by rw [he]; positivity⟩

lemma prescribedGrid_center_bound {R r : ℝ} {K : Set ℂ}
    (hK : K ⊆ closedBall 0 R) {ij : ℤ × ℤ} (hij : ij∈prescribedGridIndex R r K) :
    ‖prescribedGridCenter r ij‖  ≤  R+3*r := by
  classical
  obtain ⟨z,hz,hcell⟩ := (Finset.mem_filter.mp hij).2.2
  have hnorm : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hK hz
  have hdist : dist (prescribedGridCenter r ij) z ≤ 3*r := by
    simpa only [prescribedFineCell,mem_closedBall,dist_comm] using hcell
  have ht := dist_triangle (prescribedGridCenter r ij) z 0
  simp only [dist_zero_right] at ht
  linarith

lemma prescribedGrid_card_bound {R r : ℝ} (hR : 0 ≤ R) (hr : 0<r) (hr1 : r ≤ 1)
    (K : Set ℂ) :
    ((prescribedGridIndex R r K).card:ℝ)  ≤  (2*R+5)^2*r^(-2:ℝ) := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (coverGrid_card_bound hR hr hr1)

end SLEExactGauge

end

end OAI
