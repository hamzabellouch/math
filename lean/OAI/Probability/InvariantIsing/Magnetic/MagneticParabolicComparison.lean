import OAI.Probability.InvariantIsing.Magnetic.MagneticParabolicMinimum

namespace OAI

/-! Exponential damping removes the sign restriction on the bounded
zeroth-order coefficient in the degenerate closed-interval comparison. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma parabolic_minimum_nonneg_bounded {T M : ℝ} (hT : 0 ≤ T)
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
    (hC : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, C p ≤ M)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) T,
      A (t, -1) = 0 ∧ B (t, -1) = 0 ∧ A (t, 1) = 0 ∧ B (t, 1) = 0)
    (hPDE : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Wxx p + B p * Wx p + C p * W p ≤ Wt p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ W p := by
  let E : ℝ × ℝ → ℝ := fun p => Real.exp (-(M + 1) * p.1)
  let V := fun p => E p * W p
  let Vt := fun p => E p * (Wt p - (M + 1) * W p)
  let Vx := fun p => E p * Wx p
  let Vxx := fun p => E p * Wxx p
  have hV : ContinuousOn V (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1) :=
    ((by fun_prop : Continuous E).continuousOn).mul hW
  have hVi : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ V (0, x) := by
    intro x hx
    simpa [V, E] using hinit x hx
  have hVt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => V (q, x)) (Vt (t, x)) (Iic t) t := by
    intro t ht x hx
    have he := (((hasDerivAt_id t).const_mul (-(M + 1))).exp).hasDerivWithinAt (s := Iic t)
    convert he.mul (hdt t ht x hx) using 1
    · rfl
    · simp only [Vt, E, id_eq]
      ring
  have hVx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => V (t, y)) (Vx (t, x)) x := by
    intro t ht x hx
    exact (hdx t ht x hx).const_mul (Real.exp (-(M + 1) * t))
  have hVxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Vx (t, y)) (Vxx (t, x)) x := by
    intro t ht x hx
    exact (hdxx t ht x hx).const_mul (Real.exp (-(M + 1) * t))
  have hCn : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, C p - (M + 1) < 0 := by
    intro p hp
    linarith [hC p hp]
  have hVpde : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Vxx p + B p * Vx p + (C p - (M + 1)) * V p ≤ Vt p := by
    intro p hp
    have hh := mul_le_mul_of_nonneg_left (hPDE p hp) (Real.exp_pos (-(M + 1) * p.1)).le
    dsimp only [Vxx, Vx, V, Vt, E]
    nlinarith
  have hv := parabolic_minimum_nonneg hT V Vt Vx Vxx A B
    (fun p => C p - (M + 1)) hV hVi hVt hVx hVxx hA hCn hboundary hVpde
  intro p hp
  exact nonneg_of_mul_nonneg_right (hv p hp) (Real.exp_pos (-(M + 1) * p.1))

end InvariantIsing

end

end OAI
