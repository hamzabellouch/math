import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalNameCovers

namespace OAI

/-! # Finite entropy conditioned on a measurable observation -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_comap_eq_integral
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) =
      ∫ s, observationEntropy (condDistrib id F μ s) P ∂μ.map F := by
  have hc (a : α) :
      μ[({y | P y=a}.indicator (fun _ => (1 : ℝ))) |
        MeasurableSpace.comap F inferInstance] =ᵐ[μ]
        fun y => (condDistrib id F μ (F y)).real {z | P z=a} := by
    have H := condExp_ae_eq_integral_condDistrib_id (μ := μ) hF
      ((integrable_const (μ := μ) (1 : ℝ)).indicator (hP a))
    have hi (s : S) : (∫ z, {y | P y=a}.indicator (fun _ => (1 : ℝ)) z
        ∂condDistrib id F μ s) = (condDistrib id F μ s).real {z | P z=a} := by
      rw [integral_indicator_const _ (hP a)]
      simp only [smul_eq_mul,mul_one]
    simpa only [hi] using H
  have hall := ae_all_iff.mpr hc
  unfold conditionalSigmaEntropy
  calc
    _ = ∫ y, observationEntropy (condDistrib id F μ (F y)) P ∂μ := by
      apply integral_congr_ae
      filter_upwards [hall] with y hy
      unfold observationEntropy
      congr 1
      exact funext hy
    _ = _ := (integral_map hF.aemeasurable
      (integrable_kernel_entropy (μ.map F) (condDistrib id F μ) P hP).aestronglyMeasurable).symm

theorem conditionalSigmaEntropy_comap_nonneg
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    0 ≤ conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) := by
  rw [conditionalSigmaEntropy_comap_eq_integral μ F hF P hP]
  exact integral_nonneg fun s => observationEntropy_nonneg (condDistrib id F μ s) P hP

theorem conditionalSigmaEntropy_comap_le_reference_bad_sets
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F) (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : S → Y → Fin M) (hr : ∀ s, Measurable (r s))
    (v : S → Fin M → Fin N → α) (B : Fin N → Set Y)
    (hB : ∀ i, MeasurableSet (B i))
    (hbad : ∀ᵐ s ∂μ.map F, ∀ i, ∀ᵐ y ∂condDistrib id F μ s,
      P y i ≠ v s (r s y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) ≤
      Real.log M+(N : ℝ)*(-Real.log (1-δ))+
        (∑ i : Fin N, μ.real (B i)) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  rw [conditionalSigmaEntropy_comap_eq_integral μ F hF P
    (fun a => hP (measurableSet_singleton a))]
  have H := integral_nameEntropy_le_reference_bad_sets (μ.map F) (condDistrib id F μ)
    N M P hP r hr v B hB hbad hδ hδ1
  have hm : condDistrib id F μ ∘ₘ (μ.map F)=μ := by
    simpa only [Measure.map_id] using condDistrib_comp_map hF.aemeasurable aemeasurable_id
  simpa only [hm] using H

end DukePrimeDegree

end

end OAI
