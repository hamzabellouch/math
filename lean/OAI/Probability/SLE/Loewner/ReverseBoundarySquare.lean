import OAI.Probability.SLE.Geometry.EndpointDerivativeBound

namespace OAI

/-! Squared centered reverse coordinates have a regular derivative
even when the initial point is the boundary tip. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma reverse_centered_square_derivative {S : Set ℝ} {t : ℝ}
    (q : ℝ → ℂ) (u : ℝ → ℝ) (u' : ℝ)
    (hq : HasDerivWithinAt q (-2/(q t-(u t : ℂ))) S t)
    (hu : HasDerivWithinAt u u' S t) (hp : 0 < (q t).im) :
    HasDerivWithinAt (fun s => (q s-(u s : ℂ))^2)
      (-4-2*(u' : ℂ)*(q t-(u t : ℂ))) S t := by
  have hn : q t-(u t : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact hp.ne' hi
  have huc : HasDerivWithinAt (fun s => (u s : ℂ)) (u' : ℂ) S t := hu.ofReal_comp
  have h := (hq.sub huc).pow 2
  simp only [Pi.sub_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one] at h
  convert! h using 1
  field_simp [hn]
  ring

lemma reverse_boundary_square_estimate {T L M : ℝ} (hT : 0 ≤ T)
    (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hc : ContinuousOn q (Icc 0 T)) (huc : ContinuousOn u (Icc 0 T))
    (hq0 : q 0=(u 0 : ℂ))
    (hq : ∀ t ∈ Ioc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hu : ∀ t ∈ Ioc 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hp : ∀ t ∈ Ioc 0 T, 0 < (q t).im)
    (hb : ∀ t ∈ Ioc 0 T, |u' t| ≤ L)
    (hM : ∀ t ∈ Ioc 0 T, ‖q t-(u t : ℂ)‖ ≤ M) (hL : 0 ≤ L) :
    ∀ t ∈ Icc 0 T, ‖(q t-(u t : ℂ))^2+4*(t : ℂ)‖ ≤ (2*L*M)*t := by
  let f (t : ℝ) : ℂ := (q t-(u t : ℂ))^2+4*(t : ℂ)
  have hfc : ContinuousOn f (Icc 0 T) :=
    ((hc.sub (Complex.continuous_ofReal.comp_continuousOn huc)).pow 2).add
      (continuous_const.mul Complex.continuous_ofReal).continuousOn
  have hf0 : f 0=0 := by simp [f,hq0]
  have hfd (t : ℝ) (ht : t ∈ Ioc 0 T) : HasDerivWithinAt f
      (-2*(u' t : ℂ)*(q t-(u t : ℂ))) (Ici t) t := by
    have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      convert! (hasDerivAt_id t).ofReal_comp using 1
    have h := (reverse_centered_square_derivative q u (u' t) (hq t ht) (hu t ht) (hp t ht)).add
      ((hid.const_mul 4).hasDerivWithinAt)
    convert! h using 1
    ring
  have hbd (t : ℝ) (ht : t ∈ Ioc 0 T) :
      ‖-2*(u' t : ℂ)*(q t-(u t : ℂ))‖ ≤ 2*L*M := by
    rw [norm_mul,norm_mul,norm_neg,norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hb t ht) (by norm_num)) (hM t ht)
      (norm_nonneg _) (mul_nonneg (by norm_num) hL)
  simpa only [hf0,sub_zero,f] using norm_sub_initial_le_of_deriv_on_Ioc hT f _ hfc hfd hbd

end SLEExactGauge

end

end OAI
