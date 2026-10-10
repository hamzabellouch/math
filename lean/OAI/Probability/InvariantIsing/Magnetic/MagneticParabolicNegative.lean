import OAI.Probability.InvariantIsing.Magnetic.MagneticParabolicComparison

namespace OAI

/-! Comparison only needs a bound for the zeroth-order coefficient on the
negative set of the proposed difference. This avoids division estimates
between two different inverse curvatures at the degenerate endpoints. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma parabolic_minimum_nonneg_bounded_on_negative {T M : ℝ} (hT : 0 ≤ T)
    (W Wt Wx Wxx A B C : ℝ × ℝ → ℝ)
    (hW : ContinuousOn W (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x))
    (hdt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t)
    (hdx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x)
    (hdxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x)
    (hA : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ A p)
    (hC : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, W p < 0 → C p ≤ M)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) T,
      A (t, -1) = 0 ∧ B (t, -1) = 0 ∧ A (t, 1) = 0 ∧ B (t, 1) = 0)
    (hPDE : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Wxx p + B p * Wx p + C p * W p ≤ Wt p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ W p := by
  apply parabolic_minimum_nonneg_bounded hT W Wt Wx Wxx A B
    (fun p => min (C p) M) hW hinit hdt hdx hdxx hA
    (fun p _ => min_le_right _ _) hboundary
  intro p hp
  by_cases hn : W p < 0
  · have hc := hC p ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩ hn
    simpa only [min_eq_left hc] using hPDE p hp
  · have hm := mul_le_mul_of_nonneg_right (min_le_left (C p) M) (le_of_not_gt hn)
    linarith [hPDE p hp]

lemma inverse_curvature_difference_coefficient_bound
    {a b d ζ A K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hA : a ≤ A) (hζ : 0 ≤ ζ) (hd : |a * d| ≤ K) :
    (b + a) * (d / 2 + ζ) ≤ K + 2 * A * ζ := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hd
  have hdiff : (b + a) * d / 2 ≤ K := by
    by_cases hd0 : 0 ≤ d
    · have hp := mul_nonneg (sub_nonneg.mpr hba) hd0
      nlinarith [(le_abs_self (a * d)).trans hd]
    · have hp := mul_nonpos_of_nonneg_of_nonpos (add_nonneg hb ha) (le_of_not_ge hd0)
      linarith
  have hterm := mul_le_mul_of_nonneg_right (show b + a ≤ 2 * A by linarith) hζ
  nlinarith

end InvariantIsing

end

end OAI
