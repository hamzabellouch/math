import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.CubeModelOverlap

namespace OAI

/-! The coprimality loss for the actual early-stopped coefficients. Only
nonzero rows need be rough; the ambient support is left unchanged. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bounded_noncoprime_row_sum (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {Y R M Q : ℝ} (hY : 0 ≤ Y) (hR : 0 < R) (hM : 0 ≤ M) (_hQ : 0 ≤ Q)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ Y)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M)
    (hcard : ∀ a ∈ S, β a ≠ 0 → ((primaryPrimeFactors a).card:ℝ) ≤ Q)
    (hrough : ∀ a ∈ S, β a ≠ 0 → ∀ p ∈ primaryPrimeFactors a, R ≤ norm p) :
    (∑ a ∈ S, ∑ b ∈ S, if ¬IsCoprime a b then ‖β a‖*‖β b‖ else 0) ≤
      Q*(18*Y/R)*M*(∑ a ∈ S, ‖β a‖) := by
  calc
    _ ≤ ∑ a ∈ S, Q*(18*Y/R)*M*‖β a‖ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases haz : β a = 0
      · simp [haz]
      · have hc := noncoprime_row_card_le S hY hR
          (fun b hb => ⟨primary_ne_zero (hS b hb).1,(hS b hb).2.2⟩)
          (hS a ha).1 (hS a ha).2.1 (hrough a ha haz)
        have hc' : ((S.filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤ Q*(18*Y/R) :=
          hc.trans (mul_le_mul_of_nonneg_right (hcard a ha haz) (by positivity))
        rw [←Finset.sum_filter]
        calc
          _ ≤ ∑ _b ∈ S.filter (fun b => ¬IsCoprime a b), ‖β a‖*M := by
            apply Finset.sum_le_sum
            intro b hb
            exact mul_le_mul_of_nonneg_left (hβ b (Finset.mem_filter.mp hb).1)
              (_root_.norm_nonneg _)
          _ = ((S.filter (fun b => ¬IsCoprime a b)).card:ℝ)*(‖β a‖*M) := by simp
          _ ≤ (Q*(18*Y/R))*(‖β a‖*M) :=
            mul_le_mul_of_nonneg_right hc' (by positivity)
          _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_model_overlap {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ b → b ≤ X →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (e : Eisenstein) (j k h : ℕ) (Z Q : ℝ) (early : Bool), j ≤ h →
      0 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X l b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j k h Z Q early)
      (∑ a ∈ S, ∑ c ∈ S, if ¬IsCoprime a c then ‖β a‖*‖β c‖ else 0) ≤
        324*b^2*M^2*(Real.log X/Real.log 2)/
          min (X^ξ) (geometricBinLower (1+δ) X h) := by
  obtain ⟨M,hM,hbound⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨M,hM,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hbound hX
  intro δ l b hδ hδone hb hbX W hW e j k h Z Q early hj hR
  let S := stoppedIntervalSupport ι X l b e
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j k h Z Q early
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have hβ := (hbound W hW selected 0 l b e hb hbX).1
  have hS (a : Eisenstein) (ha : a ∈ S) := stoppedIntervalSupport_spec X l b e ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log X/Real.log 2 := div_nonneg (Real.log_nonneg hX) hlog2.le
  have hcard (a : Eisenstein) (ha : a ∈ S) (_haz : β a ≠ 0) :
      ((primaryPrimeFactors a).card:ℝ) ≤ Real.log X/Real.log 2 :=
    (primary_prime_factors_card_log (hS a ha).1).trans
      (div_le_div_of_nonneg_right (Real.log_le_log
        (norm_pos_of_ne_zero (primary_ne_zero (hS a ha).1))
        ((hS a ha).2.2.trans hbX)) hlog2.le)
  have hrough (a : Eisenstein) (ha : a ∈ S) (haz : β a ≠ 0)
      (p : Eisenstein) (hp : p ∈ primaryPrimeFactors a) :
      min (X^ξ) (geometricBinLower (1+δ) X h) ≤ norm p := by
    exact stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0
      (1+δ) Z Q W (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j k h early hj haz (primaryPrimeFactor_spec (hS a ha).1 hp).1
      (primaryPrimeFactor_spec (hS a ha).1 hp).2
  have hmass : (∑ a ∈ S, ‖β a‖) ≤ 18*b*M := by
    calc
      _ ≤ ∑ _a ∈ S, M := Finset.sum_le_sum hβ
      _ = (S.card:ℝ)*M := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (primary_support_card_le S hb (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)) hM.le
  apply (bounded_noncoprime_row_sum S β hb hR hM.le hlog hS hβ hcard hrough).trans
  calc
    _ ≤ (Real.log X/Real.log 2)*(18*b/min (X^ξ) (geometricBinLower (1+δ) X h))*M*
        (18*b*M) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
