import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply

theorem two_by_two_norm_sq_bound {s e d x y : ℝ}
    (hs : 98/100 ≤ s) (hs' : s ≤ 102/100)
    (he : 0 ≤ e) (he' : e ≤ 1/100)
    (hd : 0 ≤ d) (hd' : d ≤ 95/100)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (s*x+e*y)^2+(e*x+d*y)^2 ≤
      (s+100*e^2)^2*(x^2+y^2) := by
  have hes : 0 ≤ e*x*y := mul_nonneg (mul_nonneg he hx) hy
  have hgap : 0 ≤ 2-(s+d) := by linarith
  have hcross : 2*e*(s+d)*x*y ≤ 100*e^2*x^2+(1/25:ℝ)*y^2 := by
    nlinarith [sq_nonneg (10*e*x-(1/5:ℝ)*y), mul_nonneg hgap hes]
  have hmain : s^2+101*e^2 ≤ (s+100*e^2)^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s-98/100) (sq_nonneg e), sq_nonneg (e^2)]
  have hrest : d^2+e^2+(1/25:ℝ) ≤ (s+100*e^2)^2 := by
    have hd2 : d^2 ≤ (95/100:ℝ)^2 := by nlinarith
    have he2 : e^2 ≤ (1/100:ℝ)^2 := by nlinarith
    have hs0 : 0 ≤ s := by linarith
    nlinarith [sq_nonneg (e^2), mul_nonneg hs0 (sq_nonneg e)]
  have hm := mul_le_mul_of_nonneg_right hmain (sq_nonneg x)
  have hr := mul_le_mul_of_nonneg_right hrest (sq_nonneg y)
  nlinarith

theorem block_operator_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : WithLp 2 (ℂ × E) →L[ℂ] WithLp 2 (ℂ × F))
    {s e d : ℝ} (hs : 98/100 ≤ s) (hs' : s ≤ 102/100)
    (he : 0 ≤ e) (he' : e ≤ 1/100) (hd : 0 ≤ d) (hd' : d ≤ 95/100)
    (hfst : ∀ x, ‖(L x).fst‖ ≤ s*‖x.fst‖+e*‖x.snd‖)
    (hsnd : ∀ x, ‖(L x).snd‖ ≤ e*‖x.fst‖+d*‖x.snd‖) :
    ‖L‖ ≤ s+100*e^2 := by
  have hs0 : 0 ≤ s := by linarith
  have hb : 0 ≤ s+100*e^2 := by positivity
  refine L.opNorm_le_bound hb (fun x => ?_)
  have h1 := hfst x
  have h2 := hsnd x
  have h3 := two_by_two_norm_sq_bound hs hs' he he' hd hd'
    (norm_nonneg x.fst) (norm_nonneg x.snd)
  have hsq : ‖L x‖^2 ≤ ((s+100*e^2)*‖x‖)^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, mul_pow, WithLp.prod_norm_sq_eq_of_L2]
    have h1' : ‖(L x).fst‖^2 ≤ (s*‖x.fst‖+e*‖x.snd‖)^2 :=
      sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h1
    have h2' : ‖(L x).snd‖^2 ≤ (e*‖x.fst‖+d*‖x.snd‖)^2 :=
      sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h2
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mp hsq

end Ostmann.Supply

end

end OAI
