import Mathlib
import OAI.Probability.Ballisticity.Estimates.OrderedTimes
import OAI.Probability.Ballisticity.Estimates.SymmetrizedMgf

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
namespace DirectionalTransience

lemma isGaussian_pi_real {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ι → ℝ≥0) :
    IsGaussian (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
  let μ := Measure.pi (fun i => gaussianReal (m i) (v i))
  have h (i : ι) : HasGaussianLaw (fun x : ι → ℝ => x i) μ := by
    refine ⟨(measurable_pi_apply i).aemeasurable,?_⟩
    change IsGaussian (μ.map (fun x => x i))
    rw [(measurePreserving_eval (fun i => gaussianReal (m i) (v i)) i).map_eq]
    infer_instance
  have hi : iIndepFun (fun i (x : ι → ℝ) => x i) μ := iIndepFun_pi fun i => measurable_id.aemeasurable
  have hh := hi.hasGaussianLaw h
  have hh' : IsGaussian (μ.map id) := hh.isGaussian_map
  simpa only [Measure.map_id] using hh'

instance gaussianPathFiniteLaw_gaussian (T : ℝ) (I : Finset unitInterval) :
    IsGaussian (gaussianPathFiniteLaw T I) := by
  unfold gaussianPathFiniteLaw
  have := isGaussian_pi_real (fun _ : Fin I.card => (0:ℝ))
    (fun j => Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc)))
  infer_instance

lemma gaussianPathFiniteLaw_mean (T : ℝ) (I : Finset unitInterval) :
    ∫ x, x ∂gaussianPathFiniteLaw T I = 0 := by
  unfold gaussianPathFiniteLaw
  let μ := Measure.pi (fun j : Fin I.card => gaussianReal 0
    (Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc))))
  have : IsGaussian μ := isGaussian_pi_real _ _
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ x, incrementCumsum I (id x) ∂μ) = 0
  rw [(incrementCumsum I).integral_comp_comm IsGaussian.integrable_id]
  have hz : (∫ x, x ∂μ) = 0 := by
    ext j
    change (ContinuousLinearMap.proj j : (Fin I.card → ℝ) →L[ℝ] ℝ) (∫ x, x ∂μ) = 0
    rw [← IsGaussian.integral_dual (μ := μ) (.proj j)]
    simp [μ,integral_eval]
  simp only [id_eq,hz,map_zero]

lemma path_restrict_iid_diff (μ : Measure C(unitInterval,ℝ)) [IsProbabilityMeasure μ]
    (I : Finset unitInterval) :
    ((μ.map (fun g : C(unitInterval,ℝ) => I.restrict g)).prod (μ.map (fun g : C(unitInterval,ℝ) => I.restrict g))).map
      (fun p : (I → ℝ) × (I → ℝ) => p.1-p.2) =
    ((μ.prod μ).map (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) := by
  let L : C(unitInterval,ℝ) →L[ℝ] (I → ℝ) :=
    { toFun g := I.restrict g
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      cont := continuous_path_restrict I }
  exact map_iid_difference_linear μ L

lemma path_of_iid_difference_gaussian (G W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (hG : ((G : Measure C(unitInterval,ℝ)).prod G).map
      (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2) = W) :
    ∀ I : Finset unitInterval, IsGaussian ((G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)) := by
  intro I
  let μ := (G : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g)
  apply iid_difference_isGaussian μ (gaussianPathFiniteLaw T I) (gaussianPathFiniteLaw_mean T I)
  rw [path_restrict_iid_diff,hG,hW]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
