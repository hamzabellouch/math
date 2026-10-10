import OAI.Probability.SLE.Geometry.ComplexDissipation
import OAI.Probability.SLE.Loewner.LocalReverseCone

namespace OAI

/-! Reverse trajectories in a vertical cone have a dissipative difference
equation. The contraction includes a boundary initial point. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma reverse_coefficient_re_nonpos {q r : ℂ} {u t : ℝ}
    (ht : 0 ≤ t) (hqp : 0 ≤ q.im) (hrp : 0 ≤ r.im)
    (hqx : (q.re-u)^2 ≤ t) (hrx : (r.re-u)^2 ≤ t)
    (hqy : t ≤ q.im^2) (hry : t ≤ r.im^2) :
    (2/((q-(u : ℂ))*(r-(u : ℂ)))).re ≤ 0 := by
  have hxx : (q.re-u)*(r.re-u) ≤ t := by
    nlinarith [sq_nonneg ((q.re-u)-(r.re-u))]
  have hqroot : Real.sqrt t ≤ q.im := by
    nlinarith [Real.sq_sqrt ht,Real.sqrt_nonneg t]
  have hrroot : Real.sqrt t ≤ r.im := by
    nlinarith [Real.sq_sqrt ht,Real.sqrt_nonneg t]
  have hyy : t ≤ q.im*r.im := by
    have hh := mul_le_mul hqroot hrroot (Real.sqrt_nonneg t) hqp
    nlinarith [Real.sq_sqrt ht]
  have hreal : ((q-(u : ℂ))*(r-(u : ℂ))).re ≤ 0 := by
    simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,
      Complex.sub_im,Complex.ofReal_im,sub_zero]
    linarith
  simp only [Complex.div_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,zero_div,add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hreal)
    (Complex.normSq_nonneg _)

theorem reverse_trajectories_contract_in_cones {T : ℝ} (hT : 0 ≤ T)
    (q r : ℝ → ℂ) (u : ℝ → ℝ)
    (hqc : ContinuousOn q (Icc 0 T)) (hrc : ContinuousOn r (Icc 0 T))
    (hq : ∀ t ∈ Ioc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hr : ∀ t ∈ Ioc 0 T, HasDerivWithinAt r
      (-2/(r t-(u t : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Ioc 0 T, 0 < (q t).im)
    (hrp : ∀ t ∈ Ioc 0 T, 0 < (r t).im)
    (hqx : ∀ t ∈ Ioc 0 T, ((q t).re-u t)^2 ≤ t)
    (hrx : ∀ t ∈ Ioc 0 T, ((r t).re-u t)^2 ≤ t)
    (hqy : ∀ t ∈ Ioc 0 T, t ≤ (q t).im^2)
    (hry : ∀ t ∈ Ioc 0 T, t ≤ (r t).im^2) :
    ∀ t ∈ Icc 0 T, dist (q t) (r t) ≤ dist (q 0) (r 0) := by
  let c (t : ℝ) : ℂ := 2/((q t-(u t : ℂ))*(r t-(u t : ℂ)))
  have hn (v : ℝ → ℂ) (hp : ∀ t ∈ Ioc 0 T, 0 < (v t).im)
      (t : ℝ) (ht : t ∈ Ioc 0 T) : v t-(u t : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact (hp t ht).ne' hi
  have hd (t : ℝ) (ht : t ∈ Ioc 0 T) :
      HasDerivWithinAt (fun s => q s-r s) (c t*(q t-r t)) (Ici t) t := by
    convert! (hq t ht).sub (hr t ht) using 1
    dsimp [c]
    field_simp [hn q hqp t ht,hn r hrp t ht]
    ring
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) : (c t).re ≤ 0 :=
    reverse_coefficient_re_nonpos ht.1.le (hqp t ht).le (hrp t ht).le
      (hqx t ht) (hrx t ht) (hqy t ht) (hry t ht)
  simpa only [dist_eq_norm] using
    complex_linear_endpoint_contraction hT (fun s => q s-r s) c (hqc.sub hrc) hd hc

end SLEExactGauge

end

end OAI
