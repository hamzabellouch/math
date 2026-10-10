import OAI.NumberTheory.TwoPoint.Bounds.ComplexRawComparison
import OAI.NumberTheory.TwoPoint.Bounds.PhaseSelection

namespace OAI

/-! Numerical phase selection and the raw lower bound use the whole reciprocal
mass. No phase or nonvanishing condition is imposed on individual primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma exists_weighted_phase_subset {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (z : ι → ℂ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hdefect : (∑ i ∈ S, w i * (1 - ‖z i‖)) ≤ (∑ i ∈ S, w i) / 2) :
    ∃ A ⊆ S, (∑ i ∈ S, w i) / 8 ≤ ‖∑ i ∈ A, (w i : ℂ) * z i‖ := by
  obtain ⟨A, hAS, hA⟩ := exists_subfamily_complex_mass S (fun i => (w i : ℂ) * z i)
  refine ⟨A, hAS, ?_⟩
  have he : (∑ i ∈ S, w i * (1 - ‖z i‖)) =
      (∑ i ∈ S, w i) - ∑ i ∈ S, w i * ‖z i‖ := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hn : (∑ i ∈ S, ‖(w i : ℂ) * z i‖) = ∑ i ∈ S, w i * ‖z i‖ := by
    apply sum_congr rfl
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  rw [hn] at hA
  rw [he] at hdefect
  linarith

lemma weighted_dilated_correlation_comparison {ι : Type*} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (S : Finset ι) (w : ι → ℝ) (u : ι → ℕ) (P : ι → Finset ℕ)
    (T : ι → ℝ) (h : ℕ) (X η : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hu : ∀ i ∈ S, 0 < u i)
    (hP : ∀ i ∈ S, ∀ p ∈ P i, p.Prime)
    (hcover : ∀ i ∈ S, ∀ p, p.Prime → p ∣ u i → p ∈ P i)
    (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ i ∈ S, X * Real.exp (-η) ≤ T i / u i)
    (hhi : ∀ i ∈ S, T i / u i ≤ X) :
    ‖(∑ i ∈ S, (w i : ℂ) *
        (positivePrefix (fun n => f (u i * n) * g (u i * (n + h)))
          (⌊T i⌋₊ / u i) / (T i : ℂ))) -
      (∑ i ∈ S, (w i : ℂ) * ((f (u i) * g (u i)) / (u i : ℂ))) *
        (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ))‖ ≤
      ∑ i ∈ S, w i * ((1 / (u i : ℝ)) *
        ((4 * (∑ p ∈ P i, 1 / (p : ℝ))) + 2 * η + 1 / X) +
          4 * (P i).card / T i) := by
  rw [sum_mul, ← sum_sub_distrib]
  simp_rw [mul_assoc, ← mul_sub]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  exact mul_le_mul_of_nonneg_left
    (dilated_correlation_bin_error hfm hgm hf hg (u i) h (hu i hi) (P i)
      (hP i hi) (hcover i hi) X (T i) η hX hη (hlo i hi) (hhi i hi)) (hw i hi)

lemma raw_norm_lower_bound (R C M : ℂ) (mass γ : ℝ)
    (_hmass : 0 ≤ mass) (hγ : 0 ≤ γ)
    (hC : mass / 8 ≤ ‖C‖) (hM : γ ≤ ‖M‖)
    (herr : ‖R - C * M‖ ≤ γ * mass / 16) :
    γ * mass / 16 ≤ ‖R‖ := by
  have hprod : (mass / 8) * γ ≤ ‖C * M‖ := by
    rw [norm_mul]
    exact mul_le_mul hC hM hγ (norm_nonneg C)
  have htriangle : ‖C * M‖ ≤ ‖R‖ + ‖R - C * M‖ := by
    calc
      _ = ‖R - (R - C * M)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  linarith

end TwoPointCorrelations

end OAI
