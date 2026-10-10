import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzTests
import OAI.Analysis.RieszRectifiability.Limits.LocalLimitUniqueness

namespace OAI

/-!
# Compatibility of local L² representatives

Bounded multipliers preserve L² integrability, and supported weighted tests remove measure
restrictions. Common limiting moments then identify local representatives on overlaps
where a Lipschitz cutoff is nonzero almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem memLp_bounded_multiplier {d : ℕ} (ν : Measure (Ambient d))
    (f χ : Ambient d → ℝ) (hf : MemLp f 2 ν) (hχ : Measurable χ)
    (B : ℝ) (hB : ∀ x, |χ x| ≤ B) : MemLp (fun x => χ x * f x) 2 ν := by
  apply hf.of_le_mul (c := B) (hχ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)

theorem restricted_weighted_test_eq_integral {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Set X) (f χ ψ : X → ℝ) (hχ : ∀ x, x ∉ s → χ x = 0) :
    (∫ x, f x * (χ x * ψ x) ∂ν.restrict s) = ∫ x, f x * (χ x * ψ x) ∂ν := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [hχ x hx, zero_mul, mul_zero]

theorem local_L2_agreement_from_common_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (s t : Set (Ambient d))
    (f g : Ambient d → ℝ) (hf : MemLp f 2 (ν.restrict s)) (hg : MemLp g 2 (ν.restrict t))
    (χ : Ambient d → ℝ) (Kχ Bχ : ℝ≥0) (hχ : LipschitzWith Kχ χ)
    (hχB : ∀ x, |χ x| ≤ (Bχ : ℝ))
    (hχsupp : ∀ x, χ x ≠ 0 → x ∈ s ∩ t)
    (hχpos : ∀ᵐ x ∂ν.restrict (s ∩ t), χ x ≠ 0)
    (w : ℕ → Ambient d → ℝ)
    (hfirst : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict s) atTop
        (𝓝 (∫ x, f x * ψ x ∂ν.restrict s)))
    (hsecond : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict t) atTop
        (𝓝 (∫ x, g x * ψ x ∂ν.restrict t))) :
    f =ᵐ[ν.restrict (s ∩ t)] g := by
  have hzS : ∀ x, x ∉ s → χ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hχsupp x hne).1
  have hzT : ∀ x, x ∉ t → χ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hχsupp x hne).2
  have hzO : ∀ x, x ∉ s ∩ t → χ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hχsupp x hne)
  have hfO : MemLp f 2 (ν.restrict (s ∩ t)) :=
    hf.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hgO : MemLp g 2 (ν.restrict (s ∩ t)) :=
    hg.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have heq : (fun x => χ x * f x) =ᵐ[ν.restrict (s ∩ t)] (fun x => χ x * g x) := by
    apply L2_ae_eq_of_compact_lipschitz_pairings (ν.restrict (s ∩ t)) _ _
      (memLp_bounded_multiplier _ f χ hfO hχ.continuous.measurable Bχ hχB)
      (memLp_bounded_multiplier _ g χ hgO hχ.continuous.measurable Bχ hχB)
    intro ψ K B hc hLip hB _
    have htest : HasCompactSupport (fun x => χ x * ψ x) := hc.mul_left
    have htestLip := lipschitz_bounded_product_real hχ hLip hχB hB
    have htestB : ∀ x, |χ x * ψ x| ≤ ((Bχ * B : ℝ≥0) : ℝ) := by
      intro x
      simp only [abs_mul, NNReal.coe_mul]
      exact mul_le_mul (hχB x) (hB x) (abs_nonneg _) Bχ.coe_nonneg
    have h₁ := hfirst (fun x => χ x * ψ x) _ (Bχ * B) htest htestLip htestB
    have h₂ := hsecond (fun x => χ x * ψ x) _ (Bχ * B) htest htestLip htestB
    simp only [restricted_weighted_test_eq_integral _ s _ χ ψ hzS] at h₁
    simp only [restricted_weighted_test_eq_integral _ t _ χ ψ hzT] at h₂
    have hsame := tendsto_nhds_unique h₁ h₂
    have hleft : (fun x => (χ x * f x) * ψ x) = fun x => f x * (χ x * ψ x) := by
      funext x
      ring
    have hright : (fun x => (χ x * g x) * ψ x) = fun x => g x * (χ x * ψ x) := by
      funext x
      ring
    rw [hleft, hright, restricted_weighted_test_eq_integral _ (s ∩ t) f χ ψ hzO,
      restricted_weighted_test_eq_integral _ (s ∩ t) g χ ψ hzO]
    exact hsame
  filter_upwards [heq, hχpos] with x hx hpos
  exact (mul_left_cancel₀ hpos) hx

end

end RieszRectifiability

end OAI
