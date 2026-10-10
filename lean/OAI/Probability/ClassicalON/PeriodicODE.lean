import OAI.Probability.ClassicalON.PotentialRotation

namespace OAI

noncomputable section
open Set

namespace ClassicalON

theorem lower_second_derivative_tangent (f f' f'' : ℝ → ℝ) (a c x : ℝ)
    (h1 : ∀ t, HasDerivAt f (f' t) t) (h2 : ∀ t, HasDerivAt f' (f'' t) t)
    (hsec : ∀ t, -c ≤ f'' t) (ha : f' a = 0) :
    f a - c/2*(x-a)^2 ≤ f x := by
  let g := fun t => f t + c/2*(t-a)^2
  let g' := fun t => f' t + c*(t-a)
  let g'' := fun t => f'' t + c
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    convert (h1 t).add ((((hasDerivAt_id t).sub_const a).pow 2).const_mul (c/2)) using 1 <;>
      first | rfl | (change f' t + c * (t-a) = f' t + c/2*(2*(t-a)^(2-1)*1); ring)
  have hg' (t : ℝ) : HasDerivAt g' (g'' t) t := by
    convert (h2 t).add (((hasDerivAt_id t).sub_const a).const_mul c) using 1 <;>
      first | rfl | (change f'' t + c = f'' t + c*1; ring)
  have hcv : ConvexOn ℝ univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).hasDerivWithinAt)
      (fun t _ => (hg' t).hasDerivWithinAt)
    intro t _
    dsimp only [g'']
    linarith [hsec t]
  have hd : derivWithin g (Ioi a) a = 0 := by
    rw [(hg a).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi a)]
    simp [g', ha]
  have hm := hcv.isMinOn_of_rightDeriv_eq_zero (by simp) hd (mem_univ x)
  change f a + c/2*(a-a)^2 ≤ f x + c/2*(x-a)^2 at hm
  nlinarith

theorem periodic_ode_ratio (f f' f'' : ℝ → ℝ) (P δ : ℝ) (hP : 0 < P) (hδ : 0 ≤ δ)
    (hper : Function.Periodic f P) (hfpos : ∀ t, 0 < f t)
    (h1 : ∀ t, HasDerivAt f (f' t) t) (h2 : ∀ t, HasDerivAt f' (f'' t) t)
    (hode : ∀ t, -(δ*f t) ≤ f'' t) (x y : ℝ) :
    1 - δ*P^2/2 ≤ f x / f y := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (h1 t).continuousAt
  obtain ⟨a, ha, ham⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) P).Nonempty from ⟨0, le_rfl, hP.le⟩) hf.continuousOn
  have hmax (t : ℝ) : f t ≤ f a := by
    obtain ⟨s, hs, he⟩ := hper.exists_mem_Ioc hP t 0
    rw [he]
    exact ham ⟨hs.1.le, by simpa only [zero_add] using hs.2⟩
  have halocal : IsLocalMax f a := Filter.Eventually.of_forall hmax
  have hstationary : f' a = 0 := by rw [← (h1 a).deriv, halocal.deriv_eq_zero]
  have hsec (t : ℝ) : -(δ*f a) ≤ f'' t :=
    (neg_le_neg (mul_le_mul_of_nonneg_left (hmax t) hδ)).trans (hode t)
  obtain ⟨s, hs, he⟩ := hper.exists_mem_Ioc hP x a
  have ht := lower_second_derivative_tangent f f' f'' a (δ*f a) s h1 h2 hsec hstationary
  have hdist : (s-a)^2 ≤ P^2 := by
    apply pow_le_pow_left₀ (sub_nonneg.mpr hs.1.le)
    linarith [hs.2]
  have hnear : f a*(1-δ*P^2/2) ≤ f x := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hdist (div_nonneg (mul_nonneg hδ (hfpos a).le) (by norm_num : (0:ℝ) ≤ 2))
    nlinarith
  apply (le_div_iff₀ (hfpos y)).mpr
  by_cases hc : 0 ≤ 1-δ*P^2/2
  · exact (mul_le_mul_of_nonneg_left (hmax y) hc).trans (by simpa only [mul_comm] using hnear)
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (hfpos y).le).trans (hfpos x).le

end ClassicalON

end

end OAI
