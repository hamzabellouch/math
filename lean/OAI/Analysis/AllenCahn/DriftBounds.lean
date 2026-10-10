import OAI.Analysis.AllenCahn.PoissonEstimates

namespace OAI

noncomputable section
namespace PoissonSupport.DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology

lemma bounded_drift_lipschitz {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M C B : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ M)
    (hb : ∀ x, ‖b x‖ ≤ B)
    (hpde : ∀ x, |Laplacian.laplacian f x - fderiv ℝ f x (b x)| ≤ C) :
    ∀ x y, |f y - f x| ≤ 2 * (2 * M + C + 3) * (B + 1) * ‖y - x‖ := by
  let r : ℝ := (B + 1)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; exact inv_le_one_of_one_le₀ (by linarith)
  let F : Space n → ℝ := fun x => f (r • x)
  let b' : Space n → Space n := fun x => r • b (r • x)
  have hF : ContDiff ℝ 2 F := hf.comp (contDiff_id.const_smul r)
  have hb' (x : Space n) : ‖b' x‖ ≤ 1 := by
    dsimp [b']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc r * ‖b (r • x)‖ ≤ r * B := mul_le_mul_of_nonneg_left (hb _) hr.le
         _ ≤ 1 := by dsimp [r]; rw [inv_mul_le_iff₀ (by linarith : 0 < B + 1)]; linarith
  have hpde' (x : Space n) : |Laplacian.laplacian F x - fderiv ℝ F x (b' x)| ≤ C := by
    dsimp only [F, b']
    rw [laplacian_dilation hf, fderiv_dilation (hf.differentiable (by norm_num)),
      map_smul, smul_eq_mul]
    have he : r ^ 2 * Laplacian.laplacian f (r • x) -
        r * (r * fderiv ℝ f (r • x) (b (r • x))) =
        r ^ 2 * (Laplacian.laplacian f (r • x) - fderiv ℝ f (r • x) (b (r • x))) := by ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc r ^ 2 * |Laplacian.laplacian f (r • x) - fderiv ℝ f (r • x) (b (r • x))| ≤ r ^ 2 * C :=
           mul_le_mul_of_nonneg_left (hpde _) (sq_nonneg r)
         _ ≤ C := by nlinarith [mul_nonneg hC (show 0 ≤ 1 - r ^ 2 by nlinarith)]
  have H := bounded_unit_drift_lipschitz hF b' hM hC (fun x => hbound (r • x)) hb' hpde'
  intro x y
  have hh := H ((B + 1) • x) ((B + 1) • y)
  have he (z : Space n) : r • ((B + 1) • z) = z := by
    rw [smul_smul]; dsimp [r]; rw [inv_mul_cancel₀ (by linarith : B + 1 ≠ 0), one_smul]
  dsimp only [F] at hh
  rw [he, he, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ B + 1)] at hh
  exact hh.trans_eq (by ring)

lemma bounded_drift_gradient {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (b : Space n → Space n) {M C B : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ M)
    (hb : ∀ x, ‖b x‖ ≤ B)
    (hpde : ∀ x, |Laplacian.laplacian f x - fderiv ℝ f x (b x)| ≤ C)
    (x : Space n) :
    ‖gradient f x‖ ≤ 2 * (2 * M + C + 3) * (B + 1) := by
  have H := norm_fderiv_le_of_lip' ℝ (f := f) (x₀ := x)
    (show 0 ≤ 2 * (2 * M + C + 3) * (B + 1) by positivity)
    (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using bounded_drift_lipschitz hf b hM hC hB hbound hb hpde x y))
  simpa only [gradient, LinearIsometryEquiv.norm_map] using H

end PoissonSupport.DeGiorgi
end

end OAI
