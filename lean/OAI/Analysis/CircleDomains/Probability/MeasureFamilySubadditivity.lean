import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! The square root of pointwise 2-modulus is subadditive. This is the
quantitative form needed when discarding measures outside a compact set. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_sqrt_eq_iInf {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) :
    (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) =
      ⨅ (h : Z → ℝ≥0∞) (_ : Measurable h)
        (_ : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)),
        (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) := by
  change (ENNReal.orderIsoRpow (1/2) (by norm_num))
    (⨅ (h : Z → ℝ≥0∞) (_ : Measurable h)
      (_ : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)), ∫⁻ z, h z^2 ∂σ) = _
  simp only [OrderIso.map_iInf,ENNReal.orderIsoRpow_apply]

lemma measureFamilyModulus_sqrt_subadditive {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) (S T : Set A)
    (hcover : S ∪ T = univ) :
    (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤
      (measureFamilyModulus S Z σ (fun a => K a.val)) ^ (1/2 : ℝ) +
      (measureFamilyModulus T Z σ (fun a => K a.val)) ^ (1/2 : ℝ) := by
  rw [measureFamilyModulus_sqrt_eq_iInf σ (fun a : S => K a.val),
    measureFamilyModulus_sqrt_eq_iInf σ (fun a : T => K a.val)]
  simp_rw [ENNReal.iInf_add,ENNReal.add_iInf]
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  apply le_iInf
  intro g
  apply le_iInf
  intro hg
  apply le_iInf
  intro ga
  have hsum : ∀ a, 1 ≤ ∫⁻ z, h z+g z ∂(K a : Measure Z) := by
    intro a
    have he : a ∈ S ∪ T := hcover ▸ mem_univ a
    rcases he with has | hat
    · exact (ha ⟨a,has⟩).trans (lintegral_mono (fun _ => le_self_add))
    · exact (ga ⟨a,hat⟩).trans (lintegral_mono (fun _ => le_add_self))
  apply (ENNReal.rpow_le_rpow
    (measureFamilyModulus_le_admissible σ K (hh.add hg) hsum) (by norm_num)).trans
  simpa only [Pi.add_apply,ENNReal.rpow_two] using
    ENNReal.lintegral_Lp_add_le (μ := σ) hh.aemeasurable hg.aemeasurable (p := (2 : ℝ)) (by norm_num)

end CircleDomainRigidity

end

end OAI
