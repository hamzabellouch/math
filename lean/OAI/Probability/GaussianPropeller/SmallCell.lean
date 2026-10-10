import OAI.Probability.GaussianPropeller.Scalar

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell
variable {d:ℕ}

lemma sqrt_threshold {C:ℝ} (hC:9/(8*Real.pi)<C) :
    (3/2:ℝ)*gaussianConst < Real.sqrt C := by
  have hCp:0<C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hc0:0≤gaussianConst := by unfold gaussianConst; positivity
  have hc2:gaussianConst^2=1/(2*Real.pi) := by
    rw [gaussianConst,inv_pow,Real.sq_sqrt (by positivity),one_div]
  apply (sq_lt_sq₀ (by positivity : 0≤(3/2:ℝ)*gaussianConst) (Real.sqrt_nonneg C)).mp
  rw [mul_pow,hc2,Real.sq_sqrt hCp.le]
  have he : (3/2:ℝ)^2*(1/(2*Real.pi))=9/(8*Real.pi) := by field_simp; ring
  rwa [he]

lemma minimal_cap_three {A:Fin 4→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) (i:Fin 4) :
    ‖centroid (A i)‖/Real.sqrt (value A) ≤
      (8/3:ℝ)*(gaussian d).real (A i)*(1-(gaussian d).real (A i)) := by
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨K,hK,hcone,hP,hM⟩ := minimal_span_cone (n:=2) hA hCp hall i (by norm_num)
  have hp := active_probability_mem (by norm_num) hA hCp (hall i)
  have hb := Cap.cone_three K hK hcone (by change (gaussian 3).real K∈Set.Ioo (0:ℝ) 1; rw [hP]; exact ⟨hp.1,by linarith only [hp.2]⟩)
    (by change (gaussian 3).real K≤1/2; rw [hP]; exact hp.2)
  change (∫ x, K.indicator (fun x:Space 3=>x 0) x ∂gaussian 3) ≤
    4*gaussianConst*(gaussian 3).real K*(1-(gaussian 3).real K) at hb
  rw [hP,hM] at hb
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hCp)).mpr
  have hs := sqrt_threshold hC
  have hh := mul_le_mul_of_nonneg_right (show 4*gaussianConst ≤ (8/3:ℝ)*Real.sqrt (value A) by linarith only [hs])
    (show 0≤(gaussian d).real (A i)*(1-(gaussian d).real (A i)) by exact mul_nonneg hp.1.le (by linarith only [hp.2]))
  nlinarith only [hb,hh]

lemma minimal_cap_four {A:Fin 5→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) (i:Fin 5) :
    (929/1000:ℝ)*(‖centroid (A i)‖/Real.sqrt (value A))^2 ≤ (gaussian d).real (A i) := by
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨K,hK,hcone,hP,hM⟩ := minimal_span_cone (n:=3) hA hCp hall i (by norm_num)
  have hp := active_probability_mem (by norm_num) hA hCp (hall i)
  have hb := Cap.cone_four K hK hcone (by change 0<(gaussian 4).real K; rw [hP]; exact hp.1)
    (by change 0≤∫ x, K.indicator (fun x:Space 4=>x 0) x ∂gaussian 4; rw [hM]; positivity)
  change (∫ x, K.indicator (fun x:Space 4=>x 0) x ∂gaussian 4)^2 ≤
    (963/2500:ℝ)*(gaussian 4).real K at hb
  rw [hP,hM] at hb
  have hn:(963/2500:ℝ)*(929/1000)<9/(8*Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [Real.pi_lt_d6]
  have hh:=mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤929/1000)
  have hc:=mul_le_mul_of_nonneg_right (hn.trans hC).le hp.1.le
  rw [div_pow,Real.sq_sqrt hCp.le,←mul_div_assoc]
  apply (div_le_iff₀ hCp).mpr
  nlinarith only [hh,hc]

end GaussianPropeller.Reduction

end OAI
