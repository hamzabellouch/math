import Mathlib

namespace OAI

/-! A continuous extension of a complex Lipschitz map from a time set.
The coordinatewise real extensions suffice for the raw flow endpoint. -/
noncomputable section
open Set Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma exists_continuous_complex_extension {S : Set ℝ} {K : ℝ≥0}
    (f : ℝ → ℂ) (hf : LipschitzOnWith K f S) :
    ∃ g : ℝ → ℂ, Continuous g ∧ EqOn g f S := by
  have hre : LipschitzOnWith K (fun t => (f t).re) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      dist (f x).re (f y).re = |(f x-f y).re| := by simp [Real.dist_eq]
      _ ≤ ‖f x-f y‖ := Complex.abs_re_le_norm _
      _ ≤ K*dist x y := by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy
  have him : LipschitzOnWith K (fun t => (f t).im) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      dist (f x).im (f y).im = |(f x-f y).im| := by simp [Real.dist_eq]
      _ ≤ ‖f x-f y‖ := Complex.abs_im_le_norm _
      _ ≤ K*dist x y := by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy
  obtain ⟨r,hr,her⟩ := hre.extend_real
  obtain ⟨i,hi,hei⟩ := him.extend_real
  let g (t : ℝ) : ℂ := (r t : ℂ)+(i t : ℂ)*I
  refine ⟨g,(Complex.continuous_ofReal.comp hr.continuous).add
    ((Complex.continuous_ofReal.comp hi.continuous).mul continuous_const),?_⟩
  intro t ht
  apply Complex.ext <;> simp [g,← her ht,← hei ht]

end SLEExactGauge

end

end OAI
