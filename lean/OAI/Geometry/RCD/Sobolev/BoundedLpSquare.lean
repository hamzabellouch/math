import OAI.Geometry.RCD.Sobolev.WeakLaplacianSquare

namespace OAI

/-! # L² continuity of squares on uniformly bounded sets

The heat-variance differentiation needs the square to remain in L² while
the underlying bounded heat path varies in L².
-/

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The square of a bounded L² function is again an actual L² function. -/
def boundedLpSquare (f : Lp ℝ 2 μ) (C : ℝ) (_hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) : Lp ℝ 2 μ :=
  (show MemLp (fun x => (f x)^2) 2 μ from
    (Lp.memLp f).of_le_mul ((Lp.aestronglyMeasurable f).pow 2) (by
      filter_upwards [hf] with x hx
      change |(f x)^2| ≤ C*|f x|
      rw [abs_of_nonneg (sq_nonneg (f x))]
      calc
        f x^2 = |f x| *|f x| := by rw [← pow_two,sq_abs]
        _ ≤ C*|f x| := mul_le_mul_of_nonneg_right hx (abs_nonneg _))).toLp _

theorem boundedLpSquare_coe (f : Lp ℝ 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) :
    boundedLpSquare μ f C hC hf =ᵐ[μ] fun x => (f x)^2 := by
  unfold boundedLpSquare
  exact MemLp.coeFn_toLp _

/-- A quantitative continuity estimate requiring only L² distance and
separate bounds on the two functions. -/
theorem boundedLpSquare_sub_norm_le (f g : Lp ℝ 2 μ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (hg : ∀ᵐ x ∂μ, |g x| ≤ D) :
    ‖boundedLpSquare μ f C hC hf-boundedLpSquare μ g D hD hg‖ ≤ (C+D)*‖f-g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedLpSquare_coe μ f C hC hf,boundedLpSquare_coe μ g D hD hg,
    Lp.coeFn_sub (boundedLpSquare μ f C hC hf) (boundedLpSquare μ g D hD hg),
    Lp.coeFn_sub f g,hf,hg] with x hsf hsg hs he hfx hgx
  rw [hs,he]
  change ‖boundedLpSquare μ f C hC hf x-boundedLpSquare μ g D hD hg x‖ ≤
    (C+D)*‖f x-g x‖
  rw [hsf,hsg]
  simp only [Real.norm_eq_abs]
  calc
    |f x^2-g x^2| = |f x-g x| *|f x+g x| := by rw [sq_sub_sq,abs_mul,mul_comm]
    _ ≤ |f x-g x| *(C+D) := mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add hfx hgx)) (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- Uniform boundedness makes squaring continuous along an L² path. -/
theorem boundedLpSquare_continuousAt {F : ℝ → Lp ℝ 2 μ} {t C : ℝ} (hC : 0 ≤ C)
    (hF : ContinuousAt F t) (hb : ∀ s, ∀ᵐ x ∂μ, |F s x| ≤ C) :
    ContinuousAt (fun s => boundedLpSquare μ (F s) C hC (hb s)) t := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun s =>
    boundedLpSquare_sub_norm_le μ (F s) (F t) C C hC hC (hb s) (hb t))
  simpa only [sub_self,norm_zero,mul_zero] using
    (hF.tendsto.sub_const (F t)).norm.const_mul (C+C)

end RegularPointCoordinates

end

end OAI
