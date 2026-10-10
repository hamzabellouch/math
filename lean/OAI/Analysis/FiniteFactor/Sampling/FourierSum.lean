import OAI.Analysis.FiniteFactor.Sampling.Smoothing
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
noncomputable section

/-- Bounded characters are integrable under every probability law. -/
theorem samplingCharacter_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (v w : ℤ) :
    Integrable (fun θ => samplingCharacter v (X θ)*samplingCharacter w (Y θ)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((samplingCharacter_continuous v).measurable.comp hX).mul
      ((samplingCharacter_continuous w).measurable.comp hY)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun θ => by simp [samplingCharacter_norm])

/-- Finite Fourier polynomials require only Fourier bounds on the actual
joint law; the two input phases need not be independent. -/
theorem samplingFourier_sum_error {Ω α β : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (F : Finset α) (G : Finset β) (v : α → ℤ) (w : β → ℤ)
    (A : α → ℂ) (B : β → ℂ)
    (hA : ∀ a ∈ F, ‖A a‖ ≤ 1) (hB : ∀ b ∈ G, ‖B b‖ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hFourier : ∀ a ∈ F, ∀ b ∈ G, v a ≠ 0 ∨ w b ≠ 0 →
      ‖∫ θ, samplingCharacter (v a) (X θ)*samplingCharacter (w b) (Y θ) ∂μ‖ ≤ ε) :
    ‖(∫ θ, (∑ a ∈ F, A a*samplingCharacter (v a) (X θ)) *
          (∑ b ∈ G, B b*samplingCharacter (w b) (Y θ)) ∂μ) -
      (∑ a ∈ F, if v a = 0 then A a else 0) *
      (∑ b ∈ G, if w b = 0 then B b else 0)‖ ≤
        (F.card : ℝ)*(G.card : ℝ)*ε := by
  classical
  let τ := fun a b => ∫ θ, samplingCharacter (v a) (X θ)*samplingCharacter (w b) (Y θ) ∂μ
  let d := fun a b => if v a = 0 ∧ w b = 0 then (1 : ℂ) else 0
  have heq (a : α) (b : β) (θ : Ω) :
      (A a*samplingCharacter (v a) (X θ))*(B b*samplingCharacter (w b) (Y θ)) =
      (A a*B b)*(samplingCharacter (v a) (X θ)*samplingCharacter (w b) (Y θ)) := by ring
  have hi (a : α) (b : β) := (samplingCharacter_product_integrable μ X Y hX hY (v a) (w b)).const_mul (A a*B b)
  have hmain : (∫ θ, (∑ a ∈ F, A a*samplingCharacter (v a) (X θ)) *
      (∑ b ∈ G, B b*samplingCharacter (w b) (Y θ)) ∂μ) =
      ∑ a ∈ F, ∑ b ∈ G, A a*B b*τ a b := by
    simp_rw [sum_mul_sum, heq]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
    simp_rw [integral_finsetSum _ (fun b _ => hi _ b), integral_const_mul]
    rfl
  have hconstant : (∑ a ∈ F, if v a = 0 then A a else 0) *
      (∑ b ∈ G, if w b = 0 then B b else 0) =
      ∑ a ∈ F, ∑ b ∈ G, A a*B b*d a b := by
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    dsimp [d]
    split_ifs <;> simp_all
  have hτ (a : α) (ha : a ∈ F) (b : β) (hb : b ∈ G) : ‖τ a b-d a b‖ ≤ ε := by
    by_cases hz : v a = 0 ∧ w b = 0
    · simpa [τ,d,hz.1,hz.2,samplingCharacter_zero] using hε
    · have hn : v a ≠ 0 ∨ w b ≠ 0 := by tauto
      simpa [τ,d,hz] using hFourier a ha b hb hn
  rw [hmain,hconstant, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ a ∈ F, ‖∑ b ∈ G, A a*B b*(τ a b-d a b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ F, ∑ b ∈ G, ‖A a*B b*(τ a b-d a b)‖ :=
      sum_le_sum fun a ha => norm_sum_le _ _
    _ ≤ ∑ _a ∈ F, ∑ _b ∈ G, ε := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [norm_mul,norm_mul]
      calc
        _ ≤ 1*1*ε := by gcongr; exact hA a ha; exact hB b hb; exact hτ a ha b hb
        _ = ε := by ring
    _ = _ := by simp; ring

end
end FiniteFactor

end OAI
