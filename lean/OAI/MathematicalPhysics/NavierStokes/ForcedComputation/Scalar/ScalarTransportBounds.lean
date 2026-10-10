import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarCompositionBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDetectorBounds

namespace OAI

/-! The transported bump estimate used in each compact detector block.
All flow estimates here follow from the same two variational equations. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open scoped ContDiff BigOperators

theorem inverse_second_variation_sharp {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a (-t))) x‖ ≤ K * t * Real.exp (3 * K * t) := by
  have hb₂' (s : ℝ) (y : EuclideanPlane) :
      ‖fderiv ℝ (fderiv ℝ (fun x => -V (-s) x)) y‖ ≤ K := by
    have he := euclidean_second_fderiv_fun_neg (V (-s)) y
    have hn := norm_neg (fderiv ℝ (fderiv ℝ (V (-s))) y)
    exact (congrArg norm he).le.trans (hn.le.trans (hb₂ (-s) y))
  have h := euclidean_second_variation_sharp_operator hv.reverse hK
    (fun s y => by simpa only [fderiv_fun_neg, norm_neg] using hb₁ (-s) y)
    hb₂' (-a) x ht
  simpa only [neg_neg] using h

/-- The trace costs a factor of two in the planar Euclidean norm. -/
theorem hessian_trace_bound (f : EuclideanPlane → ℝ) (x : EuclideanPlane)
    {B : ℝ} (hB : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B) :
    |∑ j : Fin 2, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| ≤ 2 * B := by
  calc
    _ ≤ ∑ j : Fin 2, |fderiv ℝ (fderiv ℝ f) x
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 2, B := by
      apply Finset.sum_le_sum
      intro j _
      have h := (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)
      have hn : |fderiv ℝ (fderiv ℝ f) x
          (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| ≤
          ‖fderiv ℝ (fderiv ℝ f) x‖ := by
        simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using h
      exact hn.trans hB
    _ = 2 * B := by simp

/-- A block runs at most `n` periods. The inverse-flow Hessian has the
polynomial prefactor needed for the manuscript's exact rational scale. -/
theorem inverse_flow_block_bounds {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    (L n : ℕ) (hL : 0 < L)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ (L : ℝ))
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ (L : ℝ))
    (a : ℝ) (x : EuclideanPlane) {s : ℝ} (hs : 0 ≤ s) (hsn : s ≤ n) :
    ‖fderiv ℝ (Ψ a (-s)) x‖ ≤ (expansion L : ℝ) ^ n ∧
    ‖fderiv ℝ (fderiv ℝ (Ψ a (-s))) x‖ ≤
      (n : ℝ) * L * (expansion L : ℝ) ^ (3 * n) := by
  constructor
  · exact (euclidean_first_variation_reverse hv hb₁ a x hs).trans
      (exp_time_le_expansion_pow L n hsn)
  · have hK : (0 : ℝ) < L := by exact_mod_cast hL
    have hexp : Real.exp (3 * (L : ℝ) * s) ≤ (expansion L : ℝ) ^ (3 * n) := by
      have h := exp_time_le_expansion_pow L (3 * n)
        (s := 3 * s) (by push_cast; linarith)
      convert h using 1
      ring_nf
    calc
      _ ≤ (L : ℝ) * s * Real.exp (3 * L * s) :=
        inverse_second_variation_sharp hv hK hb₁ hb₂ a x hs
      _ ≤ (L : ℝ) * n * (expansion L : ℝ) ^ (3 * n) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsn (Nat.cast_nonneg L)) hexp
          (Real.exp_pos _).le (by positivity)
      _ = _ := by ring

/-- The chain rule gives exactly the scale used in the detector, before
multiplying by the dimension to take a Laplacian. -/
theorem transported_hessian_bound {g : EuclideanPlane → ℝ}
    {φ : EuclideanPlane → EuclideanPlane} (hg : ContDiff ℝ ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (x : EuclideanPlane) (C L n : ℕ)
    {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1)
    (hg₁ : ‖fderiv ℝ g (φ x)‖ ≤ (C : ℝ) * b⁻¹)
    (hg₂ : ‖fderiv ℝ (fderiv ℝ g) (φ x)‖ ≤ (C : ℝ) * b⁻¹ ^ 2)
    (hφ₁ : ‖fderiv ℝ φ x‖ ≤ (expansion L : ℝ) ^ n)
    (hφ₂ : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤
      (n : ℝ) * L * (expansion L : ℝ) ^ (3 * n)) :
    ‖fderiv ℝ (fderiv ℝ (g ∘ φ)) x‖ ≤
      (C : ℝ) * b⁻¹ ^ 2 * (1 + (n : ℝ) * L) * (expansion L : ℝ) ^ (3 * n) := by
  have hi : b⁻¹ ≤ b⁻¹ ^ 2 := by
    have h := (one_le_inv₀ hb).mpr hb₁
    nlinarith
  have hR : (1 : ℝ) ≤ expansion L := by exact_mod_cast expansion_one_le L
  have hp : ((expansion L : ℝ) ^ n) ^ 2 ≤ (expansion L : ℝ) ^ (3 * n) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hR (by omega)
  calc
    _ ≤ ((C : ℝ) * b⁻¹) * ((n : ℝ) * L * (expansion L : ℝ) ^ (3 * n)) +
        ((C : ℝ) * b⁻¹ ^ 2) * ((expansion L : ℝ) ^ n) ^ 2 :=
      scalar_second_composition_bound hg hφ x (by positivity) (by positivity)
        (by positivity) (by positivity) hg₁ hg₂ hφ₁ hφ₂
    _ ≤ ((C : ℝ) * b⁻¹ ^ 2) * ((n : ℝ) * L * (expansion L : ℝ) ^ (3 * n)) +
        ((C : ℝ) * b⁻¹ ^ 2) * (expansion L : ℝ) ^ (3 * n) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg C)) (by positivity)
      · exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end ForcedComputation.VelocityDetector

end

end OAI
