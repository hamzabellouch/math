import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteLabelTransport
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-! # Chamber relations pass to limiting horizontal directions

The compact carrier is constructed from the actual convergent multipliers.
For right translations in a unimodular group, finite measurable labels then
inherit every almost-everywhere relation satisfied before the limit.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology Pointwise

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

def rightTranslationMap (g : G) : C(G, G) := ⟨(· * g), continuous_mul_const g⟩

theorem continuous_rightTranslationMap : Continuous (rightTranslationMap : G → C(G, G)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_snd.mul continuous_fst

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

theorem finiteLabel_rightTranslations_relation
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Measure.InnerRegular μ]
    (label : G → I) (hlabel : Measurable label)
    (g h : ℕ → G) {g₀ h₀ : G}
    (hg : Tendsto g atTop (𝓝 g₀)) (hh : Tendsto h atTop (𝓝 h₀))
    (K : Set G) (hK : IsCompact K) (R : I → I → Prop)
    (hR : ∀ᶠ n in atTop, ∀ᵐ x ∂μ.restrict K, R (label (x * g n)) (label (x * h n))) :
    ∀ᵐ x ∂μ.restrict K, R (label (x * g₀)) (label (x * h₀)) := by
  let Q := (K * insert g₀ (range g)) ∪ (K * insert h₀ (range h))
  have hQ : IsCompact Q :=
    (hK.mul hg.isCompact_insert_range).union (hK.mul hh.isCompact_insert_range)
  apply finiteLabel_relation_transport label hlabel
    (fun n => rightTranslationMap (g n)) (fun n => rightTranslationMap (h n))
    (rightTranslationMap g₀) (rightTranslationMap h₀)
    (continuous_rightTranslationMap.continuousAt.tendsto.comp hg)
    (continuous_rightTranslationMap.continuousAt.tendsto.comp hh)
    (Eventually.of_forall (fun n => measurePreserving_mul_right μ (g n)))
    (Eventually.of_forall (fun n => measurePreserving_mul_right μ (h n)))
    (measurePreserving_mul_right μ g₀) (measurePreserving_mul_right μ h₀)
    K Q hQ.measurableSet hQ.measure_ne_top _ _ R hR
  · exact Eventually.of_forall (fun n x hx =>
      Or.inl ⟨x, hx, g n, Or.inr ⟨n, rfl⟩, rfl⟩)
  · exact Eventually.of_forall (fun n x hx =>
      Or.inr ⟨x, hx, h n, Or.inr ⟨n, rfl⟩, rfl⟩)

/-- Applying the translation result to `Exp (s • v)` gives the exact fixed
time flow comparison required when generic vectors approach an extremal ray. -/
theorem finiteLabel_horizontalDirections_relation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Measure.InnerRegular μ]
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → I) (hlabel : Measurable label)
    (v : ℕ → V) {v₀ : V} (hv : Tendsto v atTop (𝓝 v₀))
    (s t : ℝ) (K : Set G) (hK : IsCompact K) (R : I → I → Prop)
    (hR : ∀ᶠ n in atTop, ∀ᵐ x ∂μ.restrict K,
      R (label (x * Exp (s • v n))) (label (x * Exp (t • v n)))) :
    ∀ᵐ x ∂μ.restrict K,
      R (label (x * Exp (s • v₀))) (label (x * Exp (t • v₀))) := by
  exact finiteLabel_rightTranslations_relation μ label hlabel
    (fun n => Exp (s • v n)) (fun n => Exp (t • v n))
    (hExp.continuousAt.tendsto.comp (hv.const_smul s))
    (hExp.continuousAt.tendsto.comp (hv.const_smul t)) K hK R hR

end PolycyclicRecognition

end

end OAI
