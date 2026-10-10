import OAI.NumberTheory.Ostmann.Characters.SparseIntegerExpansion
import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedSmoothCharacterMean

namespace OAI

/-! # Applying the analytic estimate to the actual sparse coefficients -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def sparseExpandedMangoldtMean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) (X : ℝ) : ℂ :=
  sparsePrimitiveCoefficient p E t K none * smoothMangoldtMean 1 1 X +
    ∑ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone,
      sparsePrimitiveCoefficient p E t K (some ρ) * smoothMangoldtMean ρ.modulus ρ.character X

theorem sparseExpandedMangoldtMean_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C D : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (E : ∀ i, Finset (ZMod (p i))) (t : ℝ),
        (∀ i, 0 ∉ E i) → (∀ i b, -b ∈ E i ↔ b ∈ E i) →
        0 ≤ t → t ≤ 1 → (∀ i, (36 : ℝ) ≤ p i) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        ‖sparseExpandedMangoldtMean p E t (sparseTruncationDegree C L) (Real.exp (Real.exp L)) -
          sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) none *
            smoothPrincipalMain (Real.exp (Real.exp L))‖ ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [weighted_sparse_character_decay Z hD hR P hPNT C 6 D hC] with L hL
  obtain ⟨exception, he⟩ := hL
  refine ⟨exception, ?_⟩
  intro n p hp hprod E t hE hsym ht ht1 hp36 hmass hlog havoid
  have hcoeff (e : Option PrimitiveComplexCharacter) :
      ‖sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) e‖ ≤ Real.exp (6 * L) := by
    exact (sparsePrimitiveCoefficient_norm_le p E hE hsym t ht ht1 hp36 _ e).trans
      (Real.exp_le_exp.mpr (by linarith))
  exact he (sparsePrimitiveSupport p E t (sparseTruncationDegree C L)).eraseNone
    (fun ρ => sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) (some ρ))
    (sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) none)
    (fun ρ hρ => sparsePrimitiveSupport_modulus_le p E C L t hlog ρ hρ)
    (sparsePrimitiveSupport_avoids p E t _ exception havoid) (hcoeff none)
    (fun ρ _ => hcoeff (some ρ))

end Ostmann

end OAI
