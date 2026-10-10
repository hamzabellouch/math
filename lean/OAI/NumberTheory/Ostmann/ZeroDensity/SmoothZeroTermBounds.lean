import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedSmoothExplicitFormula
import OAI.NumberTheory.Ostmann.ZeroDensity.HighZeroTailBound

namespace OAI

/-! # Explicit-formula zero terms and their high-ordinate tail -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothZeroTerm_norm_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter)
    (X : ℝ) (i : ℕ) :
    ‖smoothZeroTerm Z χ X i‖ ≤
      Real.exp (((Z χ).zeros i).re * Real.log X) * P.mellinConstant *
        Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) := by
  have hs := (Z χ).in_strip i
  have hm := P.mellin_decay ((Z χ).zeros i) (by linarith) (by linarith)
  rw [smoothZeroTerm, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans_eq (by ring)

theorem selected_zero_height_count {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (S : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ))
    (hS : ∀ z ∈ S, z.1 ∈ F) (T : ℝ) (hT : 0 ≤ T) :
    ((S.filter (fun z => |((Z z.1).zeros z.2).im| ≤ T)).card : ℝ) ≤
      (P.zeroCountConstant * (Q : ℝ) ^ 2) * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
  have hsub : S.filter (fun z => |((Z z.1).zeros z.2).im| ≤ T) ⊆
      F.sigma (fun χ => (Z χ).heightIndices T) := by
    intro z hz
    obtain ⟨hzS, ht⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_sigma.mpr ⟨hS z hzS, ((Z z.1).mem_heightIndices T z.2).mpr ht⟩
  have hcard (χ : PrimitiveComplexCharacter) :
      ((Z χ).heightIndices T).card = (Z χ).count 0 T := by
    unfold ComplexZeroEnumeration.count
    rw [Finset.filter_eq_self.mpr (fun i _ => ((Z χ).in_strip i).1.le)]
  calc
    _ ≤ ((F.sigma (fun χ => (Z χ).heightIndices T)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ∑ χ ∈ F, ((Z χ).count 0 T : ℝ) := by
      rw [Finset.card_sigma, Nat.cast_sum]
      simp only [hcard]
    _ ≤ _ := P.zero_count Q hQ T hT F hF

theorem finite_high_smooth_zero_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (S : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ))
    (hS : ∀ z ∈ S, z.1 ∈ F) (T X : ℝ) (hT : 0 ≤ T) (hX : 1 ≤ X)
    (hheight : ∀ z ∈ S, T ≤ |((Z z.1).zeros z.2).im|) :
    (∑ z ∈ S, ‖smoothZeroTerm Z z.1 X z.2‖) ≤
      (X * P.mellinConstant) *
        (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
          Real.exp (-4 * Real.log (1 + T))) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpoint (z) (hz : z ∈ S) :
      ‖smoothZeroTerm Z z.1 X z.2‖ ≤ (X * P.mellinConstant) *
        Real.exp (-8 * Real.log (1 + |((Z z.1).zeros z.2).im|)) := by
    apply (smoothZeroTerm_norm_bound P z.1 X z.2).trans
    have he : Real.exp (((Z z.1).zeros z.2).re * Real.log X) ≤ X := by
      calc
        _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right ((Z z.1).in_strip z.2).2.le hlogX)
        _ = X := Real.exp_log hX0
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he P.mellinConstant_pos.le) (Real.exp_nonneg _)
  have htail := finite_high_zero_tail_bound S (fun z => |((Z z.1).zeros z.2).im|)
    (Q : ℝ) (P.zeroCountConstant * (Q : ℝ) ^ 2) T hQr
    (mul_nonneg P.zeroCountConstant_pos.le (sq_nonneg _)) hT hheight
    (selected_zero_height_count P Q hQ F hF S hS)
  calc
    _ ≤ ∑ z ∈ S, (X * P.mellinConstant) *
        Real.exp (-8 * Real.log (1 + |((Z z.1).zeros z.2).im|)) :=
      Finset.sum_le_sum hpoint
    _ = (X * P.mellinConstant) *
        ∑ z ∈ S, Real.exp (-8 * Real.log (1 + |((Z z.1).zeros z.2).im|)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (mul_nonneg hX0.le P.mellinConstant_pos.le)

end Ostmann

end OAI
