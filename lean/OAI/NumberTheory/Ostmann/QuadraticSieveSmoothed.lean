import OAI.NumberTheory.Ostmann.QuadraticSieveHeathBrownPoisson

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform
open ComplexConjugate

theorem summable_weighted_jacobi {w : ℤ → ℂ} (hw : Summable w) (q : ℕ) :
    Summable (fun m => w m * (jacobiSym m q : ℂ)) := by
  apply hw.norm.of_norm_bounded
  intro m
  rcases jacobiSym.trichotomy m q with h | h | h <;> simp [h]

theorem schwartz_summable_scaled (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : M ≠ 0) :
    Summable (fun m : ℤ => W ((m : ℝ) / M)) := by
  have h := schwartz_summable_int (dilatedSchwartz M⁻¹ (inv_ne_zero hM) W)
  simpa only [dilatedSchwartz_apply, div_eq_mul_inv, mul_comm] using h

theorem jacobi_sum_norm_sq (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (a : ℕ → ℂ) (m : ℤ) :
    ((‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ k ∈ S, a n * conj (a k) * (jacobiSym m (n * k) : ℂ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [map_sum, map_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro k hk
  rw [jacobiSym.mul_right' m (hS n hn) (hS k hk), Int.cast_mul]
  have hc : conj (jacobiSym m k : ℂ) = (jacobiSym m k : ℂ) := by simp
  rw [hc]
  ring

theorem weighted_jacobi_energy_expand {w : ℤ → ℂ} (hw : Summable w)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (a : ℕ → ℂ) :
    (∑' m : ℤ, w m * ((‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ S, ∑ k ∈ S, a n * conj (a k) *
        ∑' m : ℤ, w m * (jacobiSym m (n * k) : ℂ) := by
  have hf (n k : ℕ) : Summable (fun m : ℤ =>
      (a n * conj (a k)) * (w m * (jacobiSym m (n * k) : ℂ))) :=
    (summable_weighted_jacobi hw (n * k)).mul_left _
  calc
    _ = ∑' m : ℤ, ∑ n ∈ S, ∑ k ∈ S,
        (a n * conj (a k)) * (w m * (jacobiSym m (n * k) : ℂ)) := by
      apply tsum_congr
      intro m
      rw [jacobi_sum_norm_sq S hS]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ n ∈ S, ∑' m : ℤ, ∑ k ∈ S,
        (a n * conj (a k)) * (w m * (jacobiSym m (n * k) : ℂ)) := by
      exact Summable.tsum_finsetSum (fun n _ => (hasSum_sum (fun k (_ : k ∈ S) => (hf n k).hasSum)).summable)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Summable.tsum_finsetSum (fun k _ => hf n k)]
      simp only [tsum_mul_left]

theorem schwartz_jacobi_energy_expand (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : M ≠ 0)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (a : ℕ → ℂ) :
    (∑' m : ℤ, W ((m : ℝ) / M) *
      ((‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ S, ∑ k ∈ S, a n * conj (a k) *
        ∑' m : ℤ, W ((m : ℝ) / M) * (jacobiSym m (n * k) : ℂ) :=
  weighted_jacobi_energy_expand (schwartz_summable_scaled W M hM) S hS a

end Ostmann.QuadraticSieve

end OAI
