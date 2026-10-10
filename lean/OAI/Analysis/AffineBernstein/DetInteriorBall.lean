import Mathlib
import OAI.Analysis.AffineBernstein.TranslateDet

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DetInteriorBall

/-- Uniform two-sided determinant estimates throughout the smaller ball,
with constants independent of both solution and evaluation point. This
supplies the first regularity stage, but still not uniform ellipticity. -/
theorem normalized_det_interior_ball_producer (n : ℕ) (b : ℝ → ℝ)
    (hb : ∀ r : ℝ, 0 < r → 0 < b r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : Space n → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 (1/4 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), (hessian f x).PosDef) →
      AffineMaximalOn (Metric.ball 0 (1/4 : ℝ)) f →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), -1 ≤ f x ∧ f x ≤ 0) →
      HasLowerSectionModulus (Metric.ball 0 (1/4 : ℝ)) f b →
      ∀ a ∈ Metric.ball (0 : Space n) (1/8 : ℝ),
        c ≤ (hessian f a).det ∧ (hessian f a).det ≤ C := by
  let r : ℝ := 1/32
  let h := b r / 2
  let L : ℝ := (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * h^2 *
    Real.exp (r^2/(4*(r^2+1))) / h^(n+2)
  let U : ℝ := (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*(1:ℝ)/r)^2+1))+ (4*(1:ℝ)/r)^2))^n * h^2 *
    Real.exp ((4*(1:ℝ)/r)^2/(4*((4*(1:ℝ)/r)^2+1))) / h^(n+2)
  have hr : 0 < r := by norm_num [r]
  have hh : 0 < h := half_pos (hb r hr)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  refine ⟨1/(L+1),U+1,by positivity,by positivity,?_⟩
  intro f hf hp hm hfb hmod a ha
  have hball : Metric.closedBall a (2*r) ⊆ Metric.ball (0:Space n) (1/4 : ℝ) := by
    intro z hz
    have H := dist_triangle z a 0
    rw [Metric.mem_ball] at ha ⊢
    rw [Metric.mem_closedBall] at hz
    dsimp [r] at hz
    linarith
  have haa : a ∈ Metric.ball (0:Space n) (1/4 : ℝ) :=
    hball (Metric.mem_closedBall_self (by positivity))
  have Hupper : (hessian f a).det ≤ U := by
    apply affineMaximal_det_upper_of_section_control Metric.isOpen_ball (convex_ball _ _) hf hp hm hr hh (by norm_num) hball
    · intro x hx
      exact abs_le.mpr ⟨(hfb x hx).1,(hfb x hx).2.trans zero_le_one⟩
    · have He : 2*h=b r := by dsimp [h]; ring
      rw [He]
      exact hmod a haa r hr
  have Hlower : ((hessian f a).det)⁻¹ ≤ L :=
    affineMaximal_det_inverse_upper_at_of_modulus Metric.isOpen_ball (convex_ball _ _) hf hp hm hr
      ((Metric.closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hball) b (hb r hr) hmod
  refine ⟨?_,Hupper.trans (le_add_of_nonneg_right zero_le_one)⟩
  have hd : 0 < (hessian f a).det := (hp a haa).det_pos
  have H' := mul_le_mul_of_nonneg_left (Hlower.trans (le_add_of_nonneg_right zero_le_one)) hd.le
  rw [mul_inv_cancel₀ hd.ne'] at H'
  exact (div_le_iff₀ (by positivity : 0 < L+1)).mpr H'

end DetInteriorBall


end
end AffineBernstein
end

end OAI
