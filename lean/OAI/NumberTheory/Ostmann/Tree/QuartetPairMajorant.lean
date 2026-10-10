import OAI.NumberTheory.Ostmann.Characters.SquareCharacterMass
import OAI.NumberTheory.Ostmann.Characters.DifferenceMoment

namespace OAI

/-!
# Mean bounds for same-pair quartet majorants

The square-fiber factor costs two for one index and costs nothing when
summed over all indices. Difference convolution then multiplies masses.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance samePairFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def differenceMajorant {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (y : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * differenceMoment f g y

theorem mean_differenceMajorant_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∑ y : (ZMod p)ˣ, differenceMajorant f g y) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((∑ x : ZMod p, f x) / (Fintype.card (ZMod p)ˣ : ℝ)) *
        ((∑ x : ZMod p, g x) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have h := mean_units_differenceMoment_le f g hf hg
  simp only [differenceMajorant, ← Finset.mul_sum, hU]
  convert h using 1
  ring

noncomputable def samePairMajorant {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  differenceMajorant (fun d => squareCharacterMass (fun χ => F χ d) ρ) R y

theorem samePairMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (hF : ∀ χ d, 0 ≤ F χ d) (hR : ∀ d, 0 ≤ R d)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : 0 ≤ samePairMajorant F R ρ y := by
  exact mul_nonneg (by positivity) (differenceMoment_nonneg _ _
    (fun d => squareCharacterMass_nonneg _ (fun χ => hF χ d) ρ) hR y)

theorem squareCharacterMass_normalized_sum {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (ρ : MulChar (ZMod p) ℂ) :
    (∑ d : ZMod p, squareCharacterMass (fun χ => F χ d) ρ) /
      (Fintype.card (ZMod p)ˣ : ℝ) =
      squareCharacterMass (fun χ => (∑ d : ZMod p, F χ d) /
        (Fintype.card (ZMod p)ˣ : ℝ)) ρ := by
  unfold squareCharacterMass
  rw [Finset.sum_comm, Finset.sum_div]

/-- Small supremum for the same-pair majorant. -/
theorem samePairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (hF : ∀ χ d, 0 ≤ F χ d) (hR : ∀ d, 0 ≤ R d)
    (M H : ℝ) (hM : 0 ≤ M)
    (hFm : ∀ χ, (∑ d : ZMod p, F χ d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ M)
    (hRm : (∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ H)
    (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, samePairMajorant F R ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ 2 * M * H := by
  have h := mean_differenceMajorant_le (fun d => squareCharacterMass (fun χ => F χ d) ρ) R
    (fun d => squareCharacterMass_nonneg _ (fun χ => hF χ d) ρ) hR
  rw [squareCharacterMass_normalized_sum] at h
  apply h.trans
  apply mul_le_mul (squareCharacterMass_le_twice _ M hM hFm ρ) hRm
  · exact div_nonneg (Finset.sum_nonneg fun d _ => hR d) (Nat.cast_nonneg _)
  · positivity

/-- Bounded sum over all indices for the same-pair majorant. -/
theorem samePairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (hF : ∀ χ d, 0 ≤ F χ d) (hR : ∀ d, 0 ≤ R d)
    (S H : ℝ) (hS : 0 ≤ S)
    (hFs : (∑ χ : MulChar (ZMod p) ℂ,
      (∑ d : ZMod p, F χ d) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤ S)
    (hRm : (∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ H) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ, samePairMajorant F R ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ)) ≤ S * H := by
  calc
    _ ≤ ∑ ρ : MulChar (ZMod p) ℂ,
        squareCharacterMass (fun χ => (∑ d : ZMod p, F χ d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ρ *
        ((∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
      apply Finset.sum_le_sum
      intro ρ _
      have h := mean_differenceMajorant_le (fun d => squareCharacterMass (fun χ => F χ d) ρ) R
        (fun d => squareCharacterMass_nonneg _ (fun χ => hF χ d) ρ) hR
      rwa [squareCharacterMass_normalized_sum] at h
    _ = (∑ χ : MulChar (ZMod p) ℂ, (∑ d : ZMod p, F χ d) /
        (Fintype.card (ZMod p)ˣ : ℝ)) *
        ((∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
      rw [← Finset.sum_mul, sum_squareCharacterMass]
    _ ≤ S * H := mul_le_mul hFs hRm
      (div_nonneg (Finset.sum_nonneg fun d _ => hR d) (Nat.cast_nonneg _)) hS

end Ostmann

end OAI
