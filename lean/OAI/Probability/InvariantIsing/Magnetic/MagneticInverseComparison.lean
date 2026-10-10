import OAI.Probability.InvariantIsing.Magnetic.MagneticParabolicNegative

namespace OAI

/-! Exponent comparison for the one-dimensional inverse-curvature equation.
The coefficient bound is required only where the proposed order fails. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

theorem inverse_curvature_parabolic_comparison {T ζ η K : ℝ}
    (hT : 0 ≤ T) (hη : 0 ≤ η) (hζη : ζ ≤ η)
    (a aTime ax axx b bTime bx bxx : ℝ × ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hb : ContinuousOn b (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ s ∈ Icc (-1 : ℝ) 1, a (0, s) ≤ b (0, s))
    (hat : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun u => a (u, s)) (aTime (t, s)) (Iic t) t)
    (hbt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun u => b (u, s)) (bTime (t, s)) (Iic t) t)
    (hax : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => a (t, u)) (ax (t, s)) s)
    (hbx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => b (t, u)) (bx (t, s)) s)
    (haxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => ax (t, u)) (axx (t, s)) s)
    (hbxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => bx (t, u)) (bxx (t, s)) s)
    (ha0 : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ a p)
    (hb0 : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ b p)
    (ha1 : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, a p ≤ 1)
    (hbound : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, |a p * axx p| ≤ K)
    (hend : ∀ t ∈ Icc (0 : ℝ) T, a (t, -1) = 0 ∧ b (t, -1) = 0 ∧
      a (t, 1) = 0 ∧ b (t, 1) = 0)
    (hpa : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      aTime p = a p ^ 2 / 2 * axx p + ζ * a p ^ 2)
    (hpb : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      bTime p = b p ^ 2 / 2 * bxx p + η * b p ^ 2) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, a p ≤ b p := by
  have h := parabolic_minimum_nonneg_bounded_on_negative (M := K + 2 * η) hT
    (fun p => b p - a p) (fun p => bTime p - aTime p) (fun p => bx p - ax p)
    (fun p => bxx p - axx p) (fun p => b p ^ 2 / 2) (fun _ => 0)
    (fun p => (b p + a p) * (axx p / 2 + η))
    (hb.sub ha) (fun s hs => sub_nonneg.mpr (hinit s hs))
    (fun t ht s hs => (hbt t ht s hs).sub (hat t ht s hs))
    (fun t ht s hs => (hbx t ht s hs).sub (hax t ht s hs))
    (fun t ht s hs => (hbxx t ht s hs).sub (haxx t ht s hs))
    (fun p hp => div_nonneg (sq_nonneg _) (by norm_num))
    (fun p hp hn => by
      simpa only [mul_one] using inverse_curvature_difference_coefficient_bound
        (ha0 p hp) (hb0 p hp) (by linarith) (ha1 p hp) hη (hbound p hp))
    (fun t ht => by
      obtain ⟨haL, hbL, haR, hbR⟩ := hend t ht
      simp only [hbL, hbR, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div, and_self]) ?_
  · intro p hp
    exact sub_nonneg.mp (h p hp)
  · intro p hp
    rw [hpb p hp, hpa p hp]
    have hn := mul_nonneg (sub_nonneg.mpr hζη) (sq_nonneg (a p))
    nlinarith

end InvariantIsing

end

end OAI
