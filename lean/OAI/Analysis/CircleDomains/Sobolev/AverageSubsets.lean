import OAI.Analysis.CircleDomains.Modulus.AverageOscillation

namespace OAI

/-! Compare a smaller-set average to a larger-set average by mean oscillation. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma abs_average_sub_average_le_integral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s t : Set X} (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ∞)
    {f : X → ℝ} (hf : IntegrableOn f t μ) :
    |(⨍ x in s, f x ∂μ)-(⨍ x in t, f x ∂μ)| ≤
    (μ.real s)⁻¹ * (∫ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) := by
  have hsf : μ s ≠ ∞ := ne_top_of_le_ne_top ht (measure_mono hst)
  let : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hsf
  let : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr ht
  let : NeZero (μ.restrict s) := ⟨by simpa using hs⟩
  have he : (⨍ x in s, f x-(⨍ y in t, f y ∂μ) ∂μ) =
      (⨍ x in s, f x ∂μ)-(⨍ y in t, f y ∂μ) := by
    simpa only [Pi.sub_apply, average_const] using
      average_sub (hf.mono_set hst) (integrable_const (⨍ y in t, f y ∂μ))
  rw [← he]
  apply (abs_average_le_average_abs (μ.restrict s) _).trans
  rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_set (hf.sub (integrable_const _)).abs
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ hx => hst hx))
    (inv_nonneg.mpr measureReal_nonneg)

lemma abs_average_sub_average_le_oscillation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s t : Set X} (hst : s ⊆ t) (hs : μ s ≠ 0) (ht : μ t ≠ ∞)
    {f : X → ℝ} (hf : IntegrableOn f t μ) {C : ℝ}
    (hC : μ.real t ≤ C * μ.real s) :
    |(⨍ x in s, f x ∂μ)-(⨍ x in t, f x ∂μ)| ≤
      C*(⨍ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) := by
  have hsf : μ s ≠ ∞ := ne_top_of_le_ne_top ht (measure_mono hst)
  have hspos : 0 < μ.real s := lt_of_le_of_ne measureReal_nonneg
    ((measureReal_ne_zero_iff hsf).mpr hs).symm
  let : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr ht
  have he : (∫ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) =
      μ.real t * (⨍ x in t, |f x-(⨍ y in t, f y ∂μ)| ∂μ) := by
    simpa only [measureReal_restrict_apply_univ, smul_eq_mul] using
      (measure_smul_average (μ.restrict t) (fun x => |f x-(⨍ y in t, f y ∂μ)|)).symm
  apply (abs_average_sub_average_le_integral hst hs ht hf).trans
  rw [he, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (average_nonneg fun _ => abs_nonneg _)
  exact (inv_mul_le_iff₀ hspos).mpr (by simpa only [mul_comm] using hC)

end CircleDomainRigidity

end

end OAI
