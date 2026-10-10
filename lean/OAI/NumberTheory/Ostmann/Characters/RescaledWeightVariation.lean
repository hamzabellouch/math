import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedQuadraticInverse

namespace OAI

/-! # Uniform variation of the rescaled smooth weight -/

namespace Ostmann

open scoped BigOperators

noncomputable def rescaledPhaseWeight (Φ : ℝ → ℂ) (ξ Y : ℝ) (j : ℕ) : ℂ :=
  Φ (((j : ℝ) + ξ) / Y)

theorem rescaledPhaseWeight_variation (Φ : ℝ → ℂ) (ξ Y B D : ℝ) (N : ℕ)
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤ B + D * N / Y := by
  have hstep : ∀ j : ℕ, ‖rescaledPhaseWeight Φ ξ Y (j + 1) -
      rescaledPhaseWeight Φ ξ Y j‖ ≤ D / Y := by
    intro j
    have h := hlip ((((j + 1 : ℕ) : ℝ) + ξ) / Y) (((j : ℝ) + ξ) / Y)
    have heq : ((((j + 1 : ℕ) : ℝ) + ξ) / Y - ((j : ℝ) + ξ) / Y) = 1 / Y := by
      push_cast
      ring
    rw [heq, abs_of_pos (one_div_pos.mpr hY)] at h
    simpa only [rescaledPhaseWeight, mul_one_div] using h
  have hsum : (∑ j ∈ Finset.range (N - 1), ‖rescaledPhaseWeight Φ ξ Y (j + 1) -
      rescaledPhaseWeight Φ ξ Y j‖) ≤ (N - 1 : ℕ) * (D / Y) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard (div_nonneg hD hY.le))
  have hend := hbound (((N - 1 : ℕ) + ξ) / Y)
  unfold discreteVariation
  change ‖Φ (((N - 1 : ℕ) + ξ) / Y)‖ + _ ≤ _
  calc
    _ ≤ B + (N : ℝ) * (D / Y) := add_le_add hend hsum'
    _ = _ := by ring

theorem rescaledPhaseWeight_variation_uniform (Φ : ℝ → ℂ) (ξ Y B D C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hD : 0 ≤ D) (hN : (N : ℝ) ≤ C * Y)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤ B + D * C := by
  apply (rescaledPhaseWeight_variation Φ ξ Y B D N hY hD hbound hlip).trans
  have hn' := (div_le_iff₀ hY).mpr hN
  have hh := mul_le_mul_of_nonneg_left hn' hD
  rw [mul_div_assoc]
  linarith

end Ostmann

end OAI
