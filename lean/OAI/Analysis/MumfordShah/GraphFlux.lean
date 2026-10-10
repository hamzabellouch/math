import Mathlib
import OAI.Analysis.MumfordShah.GraphCalculus

namespace OAI

/-! MumfordShah graph flux. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Filter
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff

def graphChartHomeomorph (κ : ℝ → ℝ) (hκ : Continuous κ) : (ℝ × ℝ) ≃ₜ ℂ where
  toFun p := graphChart κ p.1 p.2
  invFun z := (z.re,z.im-κ z.re)
  left_inv p := by ext <;> simp [graphChart]
  right_inv z := by apply Complex.ext <;> simp [graphChart]
  continuous_toFun := by unfold graphChart; fun_prop
  continuous_invFun := by fun_prop

lemma graphChart_measurePreserving {κ : ℝ → ℝ} (hκ : Continuous κ) :
    MeasurePreserving (fun p : ℝ × ℝ => graphChart κ p.1 p.2) (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) := by
  have hs : MeasurePreserving (fun p : ℝ × ℝ => (p.1,κ p.1+p.2)) volume volume := by
    exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (by fun_prop) (Eventually.of_forall (fun s => map_add_left_eq_self volume (κ s)))
  have hc := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp hs
  have hf : (fun p : ℝ × ℝ => graphChart κ p.1 p.2) =
      (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm (p.1,κ p.1+p.2)) := by
    funext p
    apply Complex.ext <;> simp [graphChart]
  simpa only [Function.comp_def,← hf] using hc

lemma integral_graphChart {κ : ℝ → ℝ} (hκ : Continuous κ) {f : ℂ → ℝ} (hf : Integrable f volume) :
    (∫ z : ℂ, f z) = ∫ s : ℝ, ∫ r : ℝ, f (graphChart κ s r) := by
  have hm := graphChart_measurePreserving hκ
  have he := (graphChartHomeomorph κ hκ).measurableEmbedding
  have hi : Integrable (fun p : ℝ × ℝ => f (graphChart κ p.1 p.2)) volume :=
    (hm.integrable_comp_emb he).mpr hf
  rw [← hm.integral_comp he f]
  exact integral_prod _ hi

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma graphJump_inner_integrable {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) (hG : Continuous G) :
    Integrable (fun z => inner ℝ (G z) (graphJumpGradient κ β η z)) volume := by
  have hv := graphSource_contDiff hκ hβ hη
  have hc := graphSource_compactSupport hκ.continuous hcβ hcη
  have hgc : HasCompactSupport (gradient (graphSource κ β η)) :=
    (hc.fderiv ℝ).comp_left (map_zero (toDual ℝ ℂ).symm)
  have hg : Continuous (gradient (graphSource κ β η)) :=
    (toDual ℝ ℂ).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hi : Integrable (fun z => inner ℝ (G z) (gradient (graphSource κ β η) z)) volume := by
    apply (hG.inner hg).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hgc.isCompact
    intro z hz
    apply subset_tsupport _
    intro he
    exact hz (by simp only [he,inner_zero_right])
  have hi' := hi.indicator (graphUpper_isOpen hκ.continuous).measurableSet
  exact hi'.congr (Eventually.of_forall (fun z => by
    by_cases hz : z ∈ graphUpper κ <;> simp [graphJumpGradient,hz]))

theorem graph_jump_flux {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) (hG : ContDiff ℝ 1 G)
    (hdiv : ∀ s ∈ tsupport β, ∀ r ∈ tsupport η,
      (fderiv ℝ G (graphChart κ s r) 1).re +
        (fderiv ℝ G (graphChart κ s r) Complex.I).im = 0) :
    (∫ z : ℂ, inner ℝ (G z) (graphJumpGradient κ β η z)) =
      -(∫ s : ℝ, β s * η 0 * ((G (graphChart κ s 0)).im -
        deriv κ s * (G (graphChart κ s 0)).re)) := by
  have hDS := graphDS_integrable hκ hβ hη.continuous hG hcβ hcη
  have hDR := graphDR_integrable hκ hβ.continuous hη hG hcβ hcη
  have hDS' : Integrable (fun p : ℝ × ℝ => graphDS κ β η G p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have h := hDS.restrict (s := univ ×ˢ Ioi (0:ℝ))
    simpa only [Measure.volume_eq_prod,← Measure.prod_restrict,Measure.restrict_univ] using h
  have hDR' : Integrable (fun p : ℝ × ℝ => graphDR κ β η G p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have h := hDR.restrict (s := univ ×ˢ Ioi (0:ℝ))
    simpa only [Measure.volume_eq_prod,← Measure.prod_restrict,Measure.restrict_univ] using h
  have he (s r : ℝ) :
      inner ℝ (G (graphChart κ s r)) (gradient (graphSource κ β η) (graphChart κ s r)) =
        graphDS κ β η G s r + graphDR κ β η G s r := by
    have hh := graphDS_add_graphDR (G := G) hκ hβ hη s r
    by_cases hs : s ∈ tsupport β
    · by_cases hr : r ∈ tsupport η
      · simpa only [hdiv s hs r hr,mul_zero,add_zero] using hh.symm
      · simpa only [image_eq_zero_of_notMem_tsupport hr,mul_zero,zero_mul,add_zero] using hh.symm
    · simpa only [image_eq_zero_of_notMem_tsupport hs,zero_mul,add_zero] using hh.symm
  rw [integral_graphChart hκ.continuous (graphJump_inner_integrable hκ hβ hη hcβ hcη hG.continuous)]
  have hc : (fun s => ∫ r : ℝ, inner ℝ (G (graphChart κ s r)) (graphJumpGradient κ β η (graphChart κ s r))) =
      (fun s => ∫ r in Ioi (0:ℝ), graphDS κ β η G s r+graphDR κ β η G s r) := by
    funext s
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with r
    have hu : graphChart κ s r ∈ graphUpper κ ↔ r ∈ Ioi (0:ℝ) := by
      simp [graphUpper,graphChart]
    by_cases hr : r ∈ Ioi (0:ℝ)
    · simpa only [graphJumpGradient,indicator_of_mem (hu.mpr hr),indicator_of_mem hr] using he s r
    · simp only [graphJumpGradient,indicator_of_notMem (mt hu.mp hr),indicator_of_notMem hr,inner_zero_right]
  rw [hc,integral_integral_add hDS' hDR',integral_integral_swap hDS']
  simp_rw [graphDS_integral_zero hκ hβ hG hcβ,graphDR_integral_Ioi hη hG hcη]
  simp only [integral_zero,zero_add,integral_neg]

end MumfordShah
end

end OAI
