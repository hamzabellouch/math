import Mathlib
import OAI.Probability.Ballisticity.Walk.WeakPathEvalTendsto
import OAI.Probability.Ballisticity.Estimates.GaussianPiReal

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def pathPointMean (G : Measure C(unitInterval,ℝ)) (t : unitInterval) : ℝ :=
  ∫ g, g t ∂G

lemma path_finite_gaussian_marginal (G : ProbabilityMeasure C(unitInterval,ℝ))
    (hG : ∀ I : Finset unitInterval,
      IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)))
    (t : unitInterval) : IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g => g t)) := by
  let I : Finset unitInterval := {t}
  let μ := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)
  have : IsGaussian μ := hG I
  let L : (I → ℝ) →L[ℝ] ℝ := .proj ⟨t,by simp [I]⟩
  have he : μ.map L = (G : Measure C(unitInterval,ℝ)).map (fun g => g t) := by
    rw [Measure.map_map L.measurable (continuous_path_restrict I).measurable]
    rfl
  rw [← he]
  infer_instance

lemma path_marginal_eq_gaussian (G : ProbabilityMeasure C(unitInterval,ℝ))
    (hG : ∀ I : Finset unitInterval,
      IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)))
    (t : unitInterval) :
    (G : Measure C(unitInterval,ℝ)).map (fun g => g t) =
      gaussianReal (pathPointMean G t) (Var[fun g : C(unitInterval,ℝ) => g t; G]).toNNReal := by
  have : IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g => g t)) := path_finite_gaussian_marginal G hG t
  rw [IsGaussian.eq_gaussianReal ((G : Measure C(unitInterval,ℝ)).map (fun g => g t)) inferInstance]
  congr 1
  · exact integral_map (continuous_eval_const t).measurable.aemeasurable measurable_id.aestronglyMeasurable
  · rw [variance_map measurable_id.aemeasurable (continuous_eval_const t).measurable.aemeasurable]; rfl

lemma continuous_pathPointMean (G : ProbabilityMeasure C(unitInterval,ℝ))
    (hG : ∀ I : Finset unitInterval,
      IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g))) :
    Continuous (pathPointMean G) :=
  continuous_gaussian_path_mean G (pathPointMean G) _ (path_marginal_eq_gaussian G hG)

lemma path_finite_mean (G : ProbabilityMeasure C(unitInterval,ℝ)) (I : Finset unitInterval)
    (hG : IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g))) :
    (∫ x, x ∂(G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)) =
      I.restrict (pathPointMean G) := by
  have := hG
  ext t
  change (ContinuousLinearMap.proj t : (I → ℝ) →L[ℝ] ℝ) (∫ x, x ∂(G : Measure C(unitInterval,ℝ)).map
    (fun g : C(unitInterval,ℝ) => I.restrict g)) = pathPointMean G t
  rw [← IsGaussian.integral_dual (μ := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)) (.proj t),integral_map
    (continuous_path_restrict I).measurable.aemeasurable (by fun_prop)]
  rfl

theorem path_iid_difference_centered (G W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (hG : ((G : Measure C(unitInterval,ℝ)).prod G).map
      (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2) = W)
    (a : ℝ) (ha : a^2 = 1/2) :
    ∃ m : C(unitInterval,ℝ), (∀ t, m t = pathPointMean G t) ∧
      (G : Measure C(unitInterval,ℝ)).map (fun g => g-m) =
        (W : Measure C(unitInterval,ℝ)).map (fun g => a • g) := by
  have hg := path_of_iid_difference_gaussian G W T hW hG
  let m : C(unitInterval,ℝ) := ⟨pathPointMean G,continuous_pathPointMean G hg⟩
  refine ⟨m,fun _ => rfl,?_⟩
  apply continuous_path_measure_ext
  intro I
  let V := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)
  have hd : (V.prod V).map (fun p : (I → ℝ) × (I → ℝ) => p.1-p.2) = gaussianPathFiniteLaw T I := by
    rw [path_restrict_iid_diff,hG,hW]
  have hh := iid_difference_centered_eq_half V (gaussianPathFiniteLaw T I)
    (gaussianPathFiniteLaw_mean T I) hd a ha
  rw [path_finite_mean G I (hg I)] at hh
  rw [← hW I] at hh
  rw [Measure.map_map (show Measurable (fun x : I → ℝ => x-I.restrict (pathPointMean G)) by fun_prop)
    (continuous_path_restrict I).measurable,
    Measure.map_map (show Measurable (fun x : I → ℝ => a • x) by fun_prop)
    (continuous_path_restrict I).measurable] at hh
  rw [Measure.map_map (continuous_path_restrict I).measurable (show Measurable (fun g : C(unitInterval,ℝ) => g-m) by fun_prop),
    Measure.map_map (continuous_path_restrict I).measurable (show Measurable (fun g : C(unitInterval,ℝ) => a • g) by fun_prop)]
  exact hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
