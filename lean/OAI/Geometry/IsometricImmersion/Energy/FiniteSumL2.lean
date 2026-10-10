import OAI.Geometry.IsometricImmersion.Energy.FiniteProductL2
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothLocal.Analytic
variable {ι α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set α}

theorem finite_product_bounded_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s, ∀ x ∈ U, ‖f i x‖ ≤ B) :
    eLpNorm' (fun x => ∏ i ∈ s, f i x) (2 : ℝ) (μ.restrict U) ≤
      ‖B ^ s.card‖ₑ * (μ U) ^ (1 / (2 : ℝ)) := by
  have hdom : ∀ᵐ x ∂(μ.restrict U), ‖∏ i ∈ s, f i x‖ ≤ ‖B ^ s.card‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.norm_of_nonneg (pow_nonneg hB s.card)]
    calc
      _ ≤ ∏ i ∈ s, ‖f i x‖ := Finset.norm_prod_le s _
      _ ≤ ∏ _i ∈ s, B :=
        Finset.prod_le_prod₀ (fun index _ => norm_nonneg (f index x))
          (fun index hindex => hb index hindex x hx)
      _ = _ := Finset.prod_const B
  calc
    _ ≤ eLpNorm' (fun _ : α => B ^ s.card) (2 : ℝ) (μ.restrict U) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := by
      rw [eLpNorm'_const (B ^ s.card) (by norm_num), Measure.restrict_apply_univ]

theorem finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
    (s : Finset ι) (f : ι → α → ℝ) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s, ∀ x ∈ U, ‖f i x‖ ≤ B)
    (hm : AEStronglyMeasurable (fun x => ∏ i ∈ s, f i x) (μ.restrict U)) :
    eLpNorm (fun x => ∏ i ∈ s, f i x) 2 (μ.restrict U) ≤
      ‖B ^ s.card‖ₑ * (μ U) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hm, ENNReal.toReal_ofNat]
  exact finite_product_bounded_eLpNorm_two s f hB hU hb

theorem finite_sum_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    (C : ι → ℝ≥0∞)
    (_hm : ∀ i ∈ s, AEStronglyMeasurable (f i) (μ.restrict U))
    (hb : ∀ i ∈ s, eLpNorm (f i) 2 (μ.restrict U) ≤ C i) :
    eLpNorm (fun x => ∑ i ∈ s, f i x) 2 (μ.restrict U) ≤ ∑ i ∈ s, C i := by
  have hsum := eLpNorm_sum_le (f := f) (s := s) (μ := μ.restrict U)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact hsum.trans (Finset.sum_le_sum hb)

end SmoothLocal.Analytic

end

end OAI
