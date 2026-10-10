import OAI.Probability.SLE.Loewner.LoewnerDriverBounds

namespace OAI

/-! Elementary barriers for the reverse Loewner equation with a bounded
derivative of the driving function. The estimates are uniform in the
positive starting height. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma damped_real_barrier {T L : ℝ} (hL : 0 ≤ L)
    (x b D : ℝ → ℝ) (hx0 : x 0=0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt x
      (-2*x t/D t+b t) (Icc 0 T) t)
    (hD : ∀ t ∈ Icc 0 T, 0 < D t)
    (hb : ∀ t ∈ Icc 0 T, b t ≤ L) :
    ∀ t ∈ Icc 0 T, x t ≤ L*t := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  apply image_le_of_deriv_right_lt_deriv_boundary
    (fun s hs => (hd s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hd s ⟨hs.1,hs.2.le⟩))
    (B := fun s => L*s+ε) (B' := fun _ => L)
    (by simp only [hx0,mul_zero,zero_add]; exact hε.le)
    (fun s => by simpa using ((hasDerivAt_id s).const_mul L).add_const ε)
    (fun s hs he => ?_) ht
  have hxs : 0 < x s := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hL hs.1) hε
  have hn : -2*x s/D s < 0 := div_neg_of_neg_of_pos (by linarith) (hD s ⟨hs.1,hs.2.le⟩)
  linarith [hb s ⟨hs.1,hs.2.le⟩]

lemma damped_real_abs_barrier {T L : ℝ} (hL : 0 ≤ L)
    (x b D : ℝ → ℝ) (hx0 : x 0=0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt x
      (-2*x t/D t+b t) (Icc 0 T) t)
    (hD : ∀ t ∈ Icc 0 T, 0 < D t)
    (hb : ∀ t ∈ Icc 0 T, |b t| ≤ L) :
    ∀ t ∈ Icc 0 T, |x t| ≤ L*t := by
  intro t ht
  refine abs_le.mpr ⟨?_,damped_real_barrier hL x b D hx0 hd hD
    (fun s hs => (le_abs_self _).trans (hb s hs)) t ht⟩
  have hn := damped_real_barrier hL (fun s => -x s) (fun s => -b s) D
    (by simp [hx0]) (fun s hs => ?_) hD
    (fun s hs => (neg_le_abs _).trans (hb s hs)) t ht
  · linarith
  · convert (hd s hs).neg using 1; ring

lemma reverse_height_square_barrier {T L : ℝ}
    (x y : ℝ → ℝ)
    (hy : ∀ t ∈ Icc 0 T, 0 < y t)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y
      (2*y t/((x t)^2+(y t)^2)) (Icc 0 T) t)
    (hx : ∀ t ∈ Icc 0 T, |x t| ≤ L*t)
    (hsmall : ∀ t ∈ Icc 0 T, L^2*t ≤ 1) :
    ∀ t ∈ Icc 0 T, 2*t ≤ (y t)^2 := by
  intro t ht
  have hh := image_le_of_deriv_right_lt_deriv_boundary
    (f := fun s => -(y s)^2) (f' := fun s => -(4*(y s)^2/((x s)^2+(y s)^2)))
    (fun s hs => ((hd s hs).pow 2).neg.continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs ?_)
    (B := fun s => -2*s) (B' := fun _ => -2)
    (by nlinarith [sq_nonneg (y 0)])
    (fun s => by simpa using (hasDerivAt_id s).const_mul (-2))
    (fun s hs he => ?_) ht
  · linarith
  · convert ((hd s ⟨hs.1,hs.2.le⟩).pow 2).neg using 1; dsimp; ring
  · have hs' : s ∈ Icc 0 T := ⟨hs.1,hs.2.le⟩
    have hy2 : (y s)^2=2*s := by linarith
    have hspos : 0 < s := by nlinarith [sq_pos_of_pos (hy s hs')]
    have hxx : (x s)^2 ≤ L^2*s^2 := by
      have ha := hx s hs'
      have hb : |x s|^2 ≤ (L*s)^2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
      simpa only [sq_abs,mul_pow] using hb
    have hyp := hy s hs'
    have hden : 0 < (x s)^2+(y s)^2 := by positivity
    have hxs : (x s)^2 ≤ s := by
      have hh := mul_le_mul_of_nonneg_right (hsmall s hs') hs.1
      nlinarith
    have hp : 2 < 4*(y s)^2/((x s)^2+(y s)^2) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith
    linarith

end SLEExactGauge

end

end OAI
