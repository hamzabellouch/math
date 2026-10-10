import Mathlib
import OAI.Analysis.AffineBernstein.DualDetCompact

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedDetLower

/-- Genuine uniform determinant lower producer on the exact fixed ball used
in rigidity. All constants precede the solution. No determinant/Hessian
bound or estimate from the missing TW producer is a premise. -/
theorem normalized_det_lower_producer (n : ℕ) (b : ℝ → ℝ)
    (hb : ∀ r : ℝ, 0 < r → 0 < b r) :
    ∃ c > (0:ℝ), ∀ f : Space n → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 (1/4 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), (hessian f x).PosDef) →
      AffineMaximalOn (Metric.ball 0 (1/4 : ℝ)) f →
      HasLowerSectionModulus (Metric.ball 0 (1/4 : ℝ)) f b →
      c ≤ (hessian f 0).det := by
  let r : ℝ := 1/16
  have hr : 0 < r := by norm_num [r]
  have hbr : 0 < b r := hb r hr
  let C : ℝ := (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * (b r/2)^2 *
    Real.exp (r^2/(4*(r^2+1))) / (b r/2)^(n+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1/(C+1),by positivity,?_⟩
  intro f hf hp hm hmod
  have H : ((hessian f 0).det)⁻¹ ≤ C := affineMaximal_det_inverse_upper_of_modulus
    Metric.isOpen_ball (convex_ball _ _) hf hp hm hr
    (Metric.closedBall_subset_ball (by norm_num [r])) b (hb r hr) hmod
  have hd : 0 < (hessian f 0).det := (hp 0 (Metric.mem_ball_self (by norm_num))).det_pos
  have H' : ((hessian f 0).det)⁻¹ ≤ C+1 := H.trans (le_add_of_nonneg_right zero_le_one)
  have HM := mul_le_mul_of_nonneg_left H' hd.le
  rw [mul_inv_cancel₀ (ne_of_gt hd)] at HM
  exact (div_le_iff₀ (by positivity : 0 < C+1)).mpr HM

/-- The determinant stage of the Trudinger--Wang proof, with both constants
uniform and with the source PDE/modulus retained. This is not yet uniform
ellipticity: determinant bounds alone do not bound individual eigenvalues. -/
theorem normalized_det_two_sided_producer (n : ℕ) (b : ℝ → ℝ)
    (hb : ∀ r : ℝ, 0 < r → 0 < b r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : Space n → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 (1/4 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), (hessian f x).PosDef) →
      AffineMaximalOn (Metric.ball 0 (1/4 : ℝ)) f →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), -1 ≤ f x ∧ f x ≤ 0) →
      HasLowerSectionModulus (Metric.ball 0 (1/4 : ℝ)) f b →
      c ≤ (hessian f 0).det ∧ (hessian f 0).det ≤ C := by
  obtain ⟨c,hc,Hc⟩ := normalized_det_lower_producer n b hb
  obtain ⟨C,hC,HC⟩ := normalized_det_upper_producer n b hb
  exact ⟨c,C,hc,hC,fun f hf hp hm hfb hmod => ⟨Hc f hf hp hm hmod,HC f hf hp hm hfb hmod⟩⟩

end NormalizedDetLower



end
end AffineBernstein
end

end OAI
