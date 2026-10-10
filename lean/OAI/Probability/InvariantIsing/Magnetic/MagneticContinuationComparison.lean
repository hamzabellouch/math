import OAI.Probability.InvariantIsing.Magnetic.MagneticParabolicComparison

namespace OAI

/-! Increasing the inverse-curvature coefficient increases a convex
continued observable. This is the comparison used for conditional square means. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

theorem magnetic_continuation_coefficient_comparison {T : ℝ} (hT : 0 ≤ T)
    (U Ut Ux Uxx V Vt Vx Vxx a b : ℝ × ℝ → ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hV : ContinuousOn V (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ s ∈ Icc (-1 : ℝ) 1, U (0, s) ≤ V (0, s))
    (hUt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun r => U (r, s)) (Ut (t, s)) (Iic t) t)
    (hVt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun r => V (r, s)) (Vt (t, s)) (Iic t) t)
    (hUx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => U (t, r)) (Ux (t, s)) s)
    (hVx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => V (t, r)) (Vx (t, s)) s)
    (hUxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => Ux (t, r)) (Uxx (t, s)) s)
    (hVxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => Vx (t, r)) (Vxx (t, s)) s)
    (ha : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ a p)
    (hab : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, a p ≤ b p)
    (hconvex : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ Uxx p)
    (hbdy : ∀ t ∈ Icc (0 : ℝ) T, b (t, -1) = 0 ∧ b (t, 1) = 0)
    (hPU : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, Ut p = a p ^ 2 / 2 * Uxx p)
    (hPV : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, Vt p = b p ^ 2 / 2 * Vxx p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, U p ≤ V p := by
  have hn := parabolic_minimum_nonneg_bounded (M := 0) hT
    (fun p => V p - U p) (fun p => Vt p - Ut p)
    (fun p => Vx p - Ux p) (fun p => Vxx p - Uxx p)
    (fun p => b p ^ 2 / 2) (fun _ => 0) (fun _ => 0)
    (hV.sub hU) (fun s hs => sub_nonneg.mpr (hinit s hs))
    (fun t ht s hs => (hVt t ht s hs).sub (hUt t ht s hs))
    (fun t ht s hs => (hVx t ht s hs).sub (hUx t ht s hs))
    (fun t ht s hs => (hVxx t ht s hs).sub (hUxx t ht s hs))
    (fun p hp => div_nonneg (sq_nonneg _) (by norm_num))
    (fun p hp => le_refl 0)
    (fun t ht => by
      rcases hbdy t ht with ⟨hl, hr⟩
      simp only [hl, hr, zero_pow (by norm_num : 2 ≠ 0), zero_div, and_self]) ?_
  · intro p hp
    exact sub_nonneg.mp (hn p hp)
  · intro p hp
    have hp' : p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1 := ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
    have hs : 0 ≤ (b p) ^ 2 - (a p) ^ 2 := by
      have ha0 := ha p hp'
      have hab' := hab p hp'
      nlinarith
    have hmul := mul_nonneg hs (hconvex p hp)
    rw [hPV p hp, hPU p hp]
    simp only [zero_mul, add_zero]
    nlinarith

end InvariantIsing

end

end OAI
