import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWindowEnergy
import OAI.NumberTheory.Ostmann.Preliminaries.LocalizedMultiplicativeSieve

namespace OAI

/-! # Integrated short-window sieve for complex Dirichlet polynomials -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators SchwartzMap FourierTransform Classical

 theorem density_finite_localized_integrable (S : Finset ℕ)
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ℕ → ℂ) :
    Integrable (fun x : ℝ => ‖∑ n ∈ S, a n * W ((x - Real.log n) / h)‖ ^ 2) := by
  have hi := density_localized_square_integrable W h hh
    (fun n : S => a n) (fun n : S => Real.log n)
  have he (x : ℝ) : (∑ n : S, a n * W ((x - Real.log n) / h)) =
      ∑ n ∈ S, a n * W ((x - Real.log n) / h) :=
    Finset.sum_coe_sort S (fun n : ℕ => a n * W ((x - Real.log n) / h))
  simpa only [he] using hi

 theorem density_window_energy_integral (S : Finset ℕ)
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ℕ → ℂ) :
    (∫ x : ℝ, ∑ n ∈ S, ‖a n * W ((x - Real.log n) / h)‖ ^ 2) =
      h * (∫ x : ℝ, ‖W x‖ ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [norm_mul, mul_pow, integral_const_mul, density_shifted_window_square W h hh]
    ring
  · intro n _
    simpa only [norm_mul, mul_pow] using
      (density_shifted_window_integrable W h hh (Real.log n)).const_mul (‖a n‖ ^ 2)

 theorem density_integrated_localized_sieve (N Q : ℕ) (hQ : 1 ≤ Q)
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h)
    (hW : ∀ y, 1 ≤ |y| → W y = 0) (a : ℕ → ℂ)
    (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    (∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ‖∑ n ∈ Finset.Icc 1 N, a n * W ((x - Real.log n) / h) * χ (n : ZMod q)‖ ^ 2) ≤
        (2 * N * h + (Q : ℝ) ^ 2 + 2) * h *
          (∫ x : ℝ, ‖W x‖ ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hi : Integrable (fun x : ℝ => (2 * N * h + (Q : ℝ) ^ 2 + 2) *
      ∑ n ∈ Finset.Icc 1 N, ‖a n * W ((x - Real.log n) / h)‖ ^ 2) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro n _
    simpa only [norm_mul, mul_pow] using
      (density_shifted_window_integrable W h hh (Real.log n)).const_mul (‖a n‖ ^ 2)
  have hm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)))) hi
    (Filter.Eventually.of_forall (fun x => localized_multiplicative_sieve N Q hQ x h hh W hW a F hF))
  rw [integral_const_mul, density_window_energy_integral _ W h hh] at hm
  simpa only [mul_assoc] using hm

 theorem density_hybrid_window (N Q : ℕ) (hQ : 1 ≤ Q)
    (W : 𝓢(ℝ, ℂ)) (c h T : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hwindow : h * T ≤ 1) (hW : ∀ y, 1 ≤ |y| → W y = 0)
    (hWlower : ∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖) (a : ℕ → ℂ)
    (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    h ^ 2 * c ^ 2 * (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))‖ ^ 2) ≤
      (2 * N * h + (Q : ℝ) ^ 2 + 2) * h *
        (∫ x : ℝ, ‖W x‖ ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hint (q : ℕ) (χ : DirichletCharacter ℂ q) :
      Integrable (fun x : ℝ => ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * W ((x - Real.log n) / h)‖ ^ 2) :=
    density_finite_localized_integrable _ W h hh _
  have hpoint (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    density_height_window_bound W c h T hc hh hwindow hWlower
      (fun n : Finset.Icc 1 N => a n * χ (n.val : ZMod q))
      (fun n : Finset.Icc 1 N => Real.log n)
  have he1 (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
      (∑ n : Finset.Icc 1 N, a n * χ (n.val : ZMod q) *
        realAdditivePhase (-(Real.log n * t))) =
      ∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) *
        realAdditivePhase (-(Real.log n * t)) :=
    Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
      a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t)))
  have he2 (q : ℕ) (χ : DirichletCharacter ℂ q) (x : ℝ) :
      (∑ n : Finset.Icc 1 N, a n * χ (n.val : ZMod q) *
        W ((x - Real.log n) / h)) =
      ∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q) * W ((x - Real.log n) / h) :=
    Finset.sum_coe_sort (Finset.Icc 1 N) (fun n : ℕ =>
      a n * χ (n : ZMod q) * W ((x - Real.log n) / h))
  simp only [he1, he2] at hpoint
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 Q) (fun q _ =>
    Finset.sum_le_sum (s := F q) (fun χ _ => hpoint q χ))
  simp only [← Finset.mul_sum] at hs
  have he : (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ∫ x : ℝ, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod q) * W ((x - Real.log n) / h)‖ ^ 2) =
      ∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ‖∑ n ∈ Finset.Icc 1 N,
          a n * W ((x - Real.log n) / h) * χ (n : ZMod q)‖ ^ 2 := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun χ _ => by
        simpa only [mul_right_comm] using hint q χ)]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [mul_right_comm]
    · intro q _
      apply integrable_finsetSum
      intro χ _
      simpa only [mul_right_comm] using hint q χ
  rw [he] at hs
  exact hs.trans (density_integrated_localized_sieve N Q hQ W h hh hW a F hF)

end Ostmann

end OAI
