import OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting
import OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem common_denominator_simplex_constant {d D : ℕ} {ρ : Fin d → ℚ}
    {w : Fin d → ℕ} (hD : 0 < D) (hw : ∀ i, 0 < w i)
    (hweights : ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ)) :
    (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * (D : ℝ) ^ d =
      1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) := by
  have hprod : (∏ i, (ρ i : ℝ)) = (∏ i, (w i : ℝ)) / (D : ℝ) ^ d := by
    simp_rw [hweights]
    rw [Finset.prod_div_distrib]
    simp
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPne : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [hprod]
  field_simp

theorem tendsto_card_realWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_realWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem tendsto_card_strictWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_strictWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem strictWeightedSimplex_card_lower_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) {H : ℝ} (hH : 0 < H) :
    H ^ d / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) ≤
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) := by
  have h := strictWeightedSimplex_lower_of_limit (fun i => (ρ i : ℝ))
    (fun i => by exact_mod_cast hρ i)
    (tendsto_card_strictWeightedSimplex_rational ρ hρ) hH
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h

theorem realWeightedSimplex_card_lower_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) {H : ℝ} (hH : 0 < H) :
    H ^ d / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) ≤
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) := by
  apply (strictWeightedSimplex_card_lower_rational ρ hρ hH).trans
  have hw : ∀ i, (0 : ℝ) < (ρ i : ℝ) := fun i => by exact_mod_cast hρ i
  exact_mod_cast (Finset.card_le_card (show
    strictWeightedSimplex (fun i => (ρ i : ℝ)) H ⊆
      realWeightedSimplex (fun i => (ρ i : ℝ)) H from by
    intro a ha
    exact (mem_realWeightedSimplex hw).mpr ((mem_strictWeightedSimplex hw).mp ha).le))

end PiExponent

end OAI
