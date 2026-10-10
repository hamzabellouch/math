import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AeAcRepresentativeMeasurable
import OAI.Geometry.WeakHessian.Measure.AeDerivLevel

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.piecewise_on_eq {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m g E)
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) {s : Set X} (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂m, x ∈ s → f x = g x) :
    IsLocalWeakUpperGradient m f (s.piecewise E D) := by
  refine ⟨?_,?_,?_⟩
  · intro o R hR
    exact MemLp.piecewise hs ((hE.1 o R hR).mono_measure Measure.restrict_le_self)
      ((hD.1 o R hR).mono_measure Measure.restrict_le_self)
  · filter_upwards [hD.2.1,hE.2.1] with x hDx hEx
    by_cases hx : x ∈ s <;> simp only [Set.piecewise, hx, ↓reduceIte] <;> assumption
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_exists_ac_representative hf hπ hb,
      hE.ae_exists_ac_representative hg hπ hb, hπ.ae_ae_eval_of_ae heq] with γ hγ hr hfg
    obtain ⟨q,hq,hq0,hq1,hqeq,hqd⟩ := hγ
    obtain ⟨r,hr,_hr0,_hr1,hreq,hrd⟩ := hr
    have hder : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv q t| ≤
          ENNReal.ofReal ((s.piecewise E D) (evalReal γ t)) * metricSpeed γ t := by
      filter_upwards [hqeq,hreq,hqd,hrd,hfg,
        ae_restrict_of_ae (ae_deriv_eq_on_eq q r),
        ae_restrict_of_ae hq.ae_differentiableAt, ae_restrict_of_ae hr.ae_differentiableAt,
        ae_restrict_mem measurableSet_Icc] with t hqt hrt hd he hfg hqr hqa hra htm
      have htt : t ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using htm
      by_cases hx : evalReal γ t ∈ s
      · have heqr := hqr (hqa htt) (hra htt) (hqt.trans ((hfg hx).trans hrt.symm))
        simpa only [Set.piecewise, hx, ↓reduceIte, heqr] using he
      · simpa only [Set.piecewise, hx, ↓reduceIte] using hd
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv q t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hq.integral_deriv_eq_sub, hq0,hq1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv q t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono_ae (by simpa only [Real.enorm_eq_ofReal_abs] using hder)

lemma minimalGradients_locality {f g D E : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D)
    (hE : IsMinimalLocalWeakUpperGradient m g E)
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) {s : Set X} (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂m, x ∈ s → f x = g x) :
    ∀ᵐ x ∂m, x ∈ s → D x = E x := by
  have hfg := hD.2 _ (hD.1.piecewise_on_eq hE.1 hf hg hs heq)
  have hef : ∀ᵐ x ∂m, x ∈ s → g x = f x := by
    filter_upwards [heq] with x hx hsx
    exact (hx hsx).symm
  have hgf := hE.2 _ (hE.1.piecewise_on_eq hD.1 hg hf hs hef)
  filter_upwards [hfg,hgf] with x h₁ h₂ hx
  rw [Set.piecewise_eq_of_mem s E D hx] at h₁
  rw [Set.piecewise_eq_of_mem s D E hx] at h₂
  exact le_antisymm h₁ h₂

lemma weakGradient_locality {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) {s : Set X} (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂m, x ∈ s → f x = g x) :
    ∀ᵐ x ∂m, x ∈ s → weakGradient m f x = weakGradient m g x :=
  minimalGradients_locality (weakGradient_isMinimal hf.2) (weakGradient_isMinimal hg.2)
    hf.1.aemeasurable hg.1.aemeasurable hs heq

end WeakHessian

end
end InlinedFile0

end OAI
