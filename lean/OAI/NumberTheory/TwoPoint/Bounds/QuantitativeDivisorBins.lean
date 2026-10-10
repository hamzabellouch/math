import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeResidueBins
import OAI.NumberTheory.TwoPoint.Bounds.RescaledPrefixSums

namespace OAI

/-! Quantitative finite extraction at Y=floor(X/u), with the exact
reciprocal mass of u and the absolute exponent 1000 retained. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma finite_rescaled_prefix_bound_at (U : Finset ℕ) (a : ℕ → ℂ)
    (F : ℕ → ℕ → ℂ) (X : ℕ) (E : ℝ) (hX : 0 < X) (hE : 0 ≤ E)
    (hU : ∀ u ∈ U, 0 < u)
    (hF : ∀ u ∈ U, ‖positivePrefix (F u) (X / u) / ((X / u : ℕ) : ℂ)‖ ≤ E) :
    ‖(∑ u ∈ U, a u * positivePrefix (F u) (X / u)) / (X : ℂ)‖ ≤
      E * ∑ u ∈ U, ‖a u‖ / (u : ℝ) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  rw [sum_div]
  calc
    _ ≤ ∑ u ∈ U, ‖a u * positivePrefix (F u) (X / u) / (X : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ U, E * (‖a u‖ / (u : ℝ)) := by
      apply sum_le_sum
      intro u hu
      have hup : (0 : ℝ) < u := by exact_mod_cast hU u hu
      have hb := prefix_norm_of_average_bound (F u) (X / u) E (hF u hu)
      have hratio : ((X / u : ℕ) : ℝ) ≤ (X : ℝ) / u := Nat.cast_div_le
      have hprefix : ‖positivePrefix (F u) (X / u)‖ ≤ ((X : ℝ) / u) * E :=
        hb.trans (mul_le_mul_of_nonneg_right hratio hE)
      rw [norm_div, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (‖a u‖ * (((X : ℝ) / u) * E)) / X := by gcongr
        _ = _ := by field_simp
    _ = _ := by rw [mul_sum]

theorem quantitative_residue_bin_family (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (X l : ℕ) [NeZero l], 0 < X →
      ∀ (U : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ZMod l)
        (M : ℕ → ℝ) (τ : ℝ) (Z : ℕ → Finset ℕ),
      0 < τ → τ < 2 → (∀ u ∈ U, 0 < u) →
      (∀ u ∈ U, Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ ((X / u : ℕ) : ℝ)) →
      (∀ u ∈ U, ∀ z ∈ Z u, M u ≤ (z : ℝ) ∧ (z : ℝ) ≤ τ * M u ∧
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ Real.exp (2 * L) ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖(∑ u ∈ U, a u * positivePrefix (residueScaledRoughProfile l (b u) (Z u) h) (X / u)) /
        (X : ℂ)‖ ≤
        ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) * (∑ u ∈ U, ‖a u‖ / (u : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := quantitative_residue_bin hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro X l _ hX U a b M τ Z hτ hτtwo hU hY hZ
  exact finite_rescaled_prefix_bound_at U a
    (fun u => residueScaledRoughProfile l (b u) (Z u) h) X _ hX (by positivity) hU
    (fun u hu => hb (X / u) l (hY u hu) (b u) (M u) τ hτ hτtwo (Z u) (hZ u hu))

end TwoPointCorrelations

end OAI
