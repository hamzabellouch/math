import Mathlib

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real

lemma mul_exp_neg_le {x y δ : ℝ} (hx : 0<x) (hxy : x≤y) (hδ : 1≤δ*x) :
    y*exp (-δ*y)≤x*exp (-δ*x) := by
  have hx0 : x≠0 := ne_of_gt hx
  have hr : y/x≤δ*(y-x)+1 := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hδ)]
  have he : y/x≤exp (δ*(y-x)) := hr.trans (add_one_le_exp _)
  calc
    y*exp (-δ*y) = (y/x)*(x*exp (-δ*y)) := by field_simp
    _ ≤ exp (δ*(y-x))*(x*exp (-δ*y)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = x*exp (-δ*x) := by
      rw [mul_left_comm,←exp_add]
      congr 2
      ring

lemma sqrt_prefactor_identity {x a p c d δ : ℝ} (hx : 0<x) :
    (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) =
      (a/sqrt x+p*sqrt (c/x+d))*(x*exp (-δ*x)) := by
  have hs : sqrt x≠0 := ne_of_gt (sqrt_pos.mpr hx)
  have he : c/x+d=(c+d*x)/x := by field_simp
  rw [he,sqrt_div' _ hx.le]
  have hh := sq_sqrt hx.le
  field_simp
  rw [hh]
  ring

lemma sqrt_exp_antitone {x y a p c d δ : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hp : 0≤p) (hc : 0≤c) (hδ : 1≤δ*x) :
    (a+p*sqrt (c+d*y))*sqrt y*exp (-δ*y) ≤
      (a+p*sqrt (c+d*x))*sqrt x*exp (-δ*x) := by
  have hy : 0<y := hx.trans_le hxy
  rw [sqrt_prefactor_identity hy,sqrt_prefactor_identity hx]
  have hfactor : a/sqrt y+p*sqrt (c/y+d) ≤ a/sqrt x+p*sqrt (c/x+d) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_left ha (sqrt_pos.mpr hx) (sqrt_le_sqrt hxy)
    · apply mul_le_mul_of_nonneg_left _ hp
      apply sqrt_le_sqrt
      simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_left hc hx hxy) d
  exact mul_le_mul hfactor (mul_exp_neg_le hx hxy hδ) (by positivity) (by positivity)
end AtomicTriangular.Envelope
end

end OAI
