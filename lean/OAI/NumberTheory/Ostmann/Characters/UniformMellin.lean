import OAI.NumberTheory.Ostmann.Tree.ReciprocalDiagonal

namespace OAI

/-!
# The uniform Mellin estimate

The positive-difference form of equation `src42` follows by combining
Mellin Parseval on the diagonal with the reciprocal affine bound.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def pairAutocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℂ :=
  (p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ) *
    additiveAutocorrelation (characterTwist g χ) d

theorem mellinDiagonalCoefficient_eq_fourier {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    mellinDiagonalCoefficient (bottomPairValue g)
      (fun d : (ZMod p)ˣ => η d * ZMod.stdAddChar (-(a * (d : ZMod p)))) χ =
        additiveFourier (fun d => pairAutocorrelation g χ d * χ d * η d) a := by
  let F : ZMod p → ℂ := fun d =>
    pairAutocorrelation g χ d * χ d * η d * ZMod.stdAddChar (-(a * d))
  have hF0 : F 0 = 0 := by simp only [F, MulChar.map_zero, mul_zero, zero_mul]
  unfold mellinDiagonalCoefficient
  calc
    _ = (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, F d := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      rw [bottomPair_mellin_autocorrelation]
      dsimp [F, pairAutocorrelation]
      ring
    _ = (p : ℂ)⁻¹ * ∑ d : ZMod p, F d := by
      rw [sum_units_eq_sum_of_zero F hF0]
    _ = _ := by simp only [F, additiveFourier_apply, mul_comm a]

theorem bottomPair_diagonal_norm_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖mellinDiagonalCoefficient (bottomPairValue g)
        (fun d : (ZMod p)ˣ => η d * ZMod.stdAddChar (-(a * (d : ZMod p)))) χ‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (‖additiveFourier (fun x => g x * η x) a‖ ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  let G := reciprocalTwist g η a
  have hG0 : G 0 = 0 := reciprocalTwist_zero g hg η a
  have hG : (∑ x : ZMod p, ‖G x‖ ^ 2) ≤ (p : ℝ) := by
    rw [show (∑ x : ZMod p, ‖G x‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 from
      reciprocalTwist_energy g hg η a]
    exact henergy
  have hc : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  rw [mellinDiagonal_parseval]
  simp_rw [mellinDiagonal_reciprocal g hg, norm_mul, Complex.norm_conj,
    norm_mulChar_unit, one_mul]
  have hinv : (∑ t : (ZMod p)ˣ,
      ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G ((t : ZMod p)⁻¹)‖ ^ 2) =
      ∑ t : (ZMod p)ˣ, ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G t‖ ^ 2 := by
    have h := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
      (fun t : (ZMod p)ˣ => ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G t‖ ^ 2)
    change (∑ t : (ZMod p)ˣ,
      ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G ((t⁻¹ : (ZMod p)ˣ) : ZMod p)‖ ^ 2) = _ at h
    simpa only [Units.val_inv_eq_inv_val] using h
  change (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
    (∑ t : (ZMod p)ˣ, ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G
      ((t : ZMod p)⁻¹)‖ ^ 2) ≤ _
  rw [hinv, hc]
  have h := affineAverage_self_correlation_unit_bound G hG0 hG
  rw [show fieldMean G = additiveFourier (fun x => g x * η x) a from
    reciprocalTwist_mean g η a] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Equation `src42` with the positive difference convention. -/
theorem uniform_mellin_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun d => pairAutocorrelation g χ d * χ d * η d) a‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (‖additiveFourier (fun x => g x * η x) a‖ ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  simpa only [mellinDiagonalCoefficient_eq_fourier] using
    bottomPair_diagonal_norm_bound g hg henergy η a

/-- The mixed Fourier hypothesis gives the paper's explicit epsilon bound. -/
theorem uniform_mellin_bound_of_fourier_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : ∀ (χ : MulChar (ZMod p) ℂ) (a : ZMod p),
      ‖additiveFourier (fun x => g x * χ x) a‖ ≤ ε)
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun d => pairAutocorrelation g χ d * χ d * η d) a‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  have hden : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    linarith
  exact (uniform_mellin_bound g hg henergy η a).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hε η a) 4) le_rfl)
      (div_nonneg (Nat.cast_nonneg p) hden))

end Ostmann

end OAI
