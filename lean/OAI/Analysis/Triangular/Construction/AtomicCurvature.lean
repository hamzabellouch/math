import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
namespace AtomicTriangular.Envelope
open Real Set

lemma linear_sqrt_exp_hasDerivAt {a b δ x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y : ℝ => (a+b*y)*sqrt y*exp (-δ*y))
      ((b*sqrt x+(a+b*x)/(2*sqrt x)-δ*((a+b*x)*sqrt x))*exp (-δ*x)) x := by
  have hd := (((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).mul
    (hasDerivAt_sqrt (ne_of_gt hx))).mul
    (((hasDerivAt_id x).const_mul (-δ)).exp)
  convert hd using 1 <;> first | rfl | (dsimp; ring)

lemma linear_sqrt_exp_antitone {a b δ x y : ℝ} (hx : 0<x) (hxy : x≤y)
    (ha : 0≤a) (hb : 0≤b) (hδ : 3/2≤δ*x) :
    (a+b*y)*sqrt y*exp (-δ*y) ≤ (a+b*x)*sqrt x*exp (-δ*x) := by
  have hδ0 : 0<δ := by nlinarith
  have hanti : AntitoneOn (fun u : ℝ => (a+b*u)*sqrt u*exp (-δ*u)) (Ici x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici x)
    · exact (by fun_prop : ContinuousOn (fun u : ℝ => (a+b*u)*sqrt u*exp (-δ*u)) (Ici x))
    · intro u hu
      exact (linear_sqrt_exp_hasDerivAt (a:=a) (b:=b) (δ:=δ) (hx.trans_le (mem_Ici.mp (interior_subset hu)))).differentiableAt.differentiableWithinAt
    · intro u hu
      have hux : x≤u := mem_Ici.mp (interior_subset hu)
      have hu0 := hx.trans_le hux
      rw [(linear_sqrt_exp_hasDerivAt (a:=a) (b:=b) (δ:=δ) hu0).deriv]
      apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
      have hs := sq_sqrt hu0.le
      have hsp : 0<sqrt u := sqrt_pos.mpr hu0
      have hδu : 3/2≤δ*u := hδ.trans (mul_le_mul_of_nonneg_left hux hδ0.le)
      apply nonpos_of_mul_nonpos_left (b:=2*sqrt u) _ (by positivity)
      have he : (b*sqrt u+(a+b*u)/(2*sqrt u)-δ*((a+b*u)*sqrt u))*(2*sqrt u) =
          a+3*b*u-2*δ*u*(a+b*u) := by
        field_simp
        rw [hs]
        ring
      rw [he]
      have h1 := mul_nonneg (show 0≤2*δ*u-1 by linarith) ha
      have h2 := mul_nonneg (show 0≤2*δ*u-3 by linarith) (mul_nonneg hb hu0.le)
      nlinarith
  exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hxy) hxy
end AtomicTriangular.Envelope
end

end OAI
