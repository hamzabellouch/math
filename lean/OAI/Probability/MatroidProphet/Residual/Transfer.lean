import OAI.Probability.MatroidProphet.Residual.Tail
import OAI.Probability.MatroidProphet.Residual.Comparison

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

noncomputable def tripleMaskExpectation (p q r : α → ℝ) (V : Finset α)
    (f : Finset α → Finset α → Finset α → ℝ) : ℝ :=
  bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (f D C)))

lemma tripleMaskExpectation_mono (p q r : α → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (V : Finset α) {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T ≤ g D C T) :
    tripleMaskExpectation p q r V f ≤ tripleMaskExpectation p q r V g := by
  apply bitsExpectation_mono p hp0 hp1
  intro D hD
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  exact bitsExpectation_mono r hr0 hr1 V (fun T hT => h D hD C hC T hT)

lemma tripleMaskExpectation_add (p q r : α → ℝ) (V : Finset α)
    (f g : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => f D C T + g D C T) =
      tripleMaskExpectation p q r V f + tripleMaskExpectation p q r V g := by
  simp only [tripleMaskExpectation, bitsExpectation_add]

lemma tripleMaskExpectation_mul (p q r : α → ℝ) (V : Finset α) (c : ℝ)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => c * f D C T) =
      c * tripleMaskExpectation p q r V f := by
  simp only [tripleMaskExpectation, bitsExpectation_mul_const]

lemma tripleMask_sample_to_rank (p q r : α → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (V : Finset α) (σ z error : Finset α → Finset α → Finset α → ℝ)
    (Y : ℝ)
    (hdet : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, σ D C T ≤ densityThreshold * z D C T + error D C T)
    (hsafe : retainedFraction * Y - (V.card : ℝ) / densityThreshold ≤ tripleMaskExpectation p q r V σ)
    (herr : tripleMaskExpectation p q r V error ≤ 2 * residualDelta * V.card) :
    (retainedFraction * Y - ((2 : ℝ)^23)⁻¹ * V.card) / densityThreshold ≤
      tripleMaskExpectation p q r V z := by
  have hcompare := tripleMaskExpectation_mono p q r hp0 hp1 hq0 hq1 hr0 hr1 V hdet
  rw [tripleMaskExpectation_add, tripleMaskExpectation_mul] at hcompare
  have hc := mul_le_mul_of_nonneg_right residual_error_constant (Nat.cast_nonneg V.card)
  have hkpos : 0 < densityThreshold := constants_positive.2.1
  apply (div_le_iff₀ hkpos).2
  rw [div_eq_mul_inv] at hsafe
  nlinarith

end MatroidProphet

end OAI
