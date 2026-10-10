import Mathlib
import OAI.Analysis.HardSphere.Operators.Regularize
import OAI.Analysis.HardSphere.Bridges.GaussianPacking

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def normCubeMean : ℝ := ∫w : C(Time,ℝ),‖w‖^3 ∂wiener
lemma integrable_normCube : Integrable (fun w : C(Time,ℝ) ↦ ‖w‖^3) wiener :=
  (IsGaussian.memLp_id wiener 3 (by norm_num)).integrable_norm_pow (by norm_num)
lemma normCubeMean_nonneg : 0≤normCubeMean := integral_nonneg (fun _ ↦ by positivity)

lemma prefix_wiener_law (u : Time) : wiener.map (prefixMap u)=wiener.map (fun w ↦ Real.sqrt (u:ℝ) • w) := by
  rw [wiener,Measure.map_map (prefixMap u).continuous.measurable measurable_path,
    Measure.map_map (by fun_prop) measurable_path]
  exact prefix_law u

lemma prefix_normCube_integrable (u : Time) :
    Integrable (fun w : C(Time,ℝ) ↦ ‖prefixMap u w‖^3) wiener :=
  ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp (prefixMap u)).integrable_norm_pow (by norm_num)

lemma prefix_normCube (u : Time) :
    ∫w : C(Time,ℝ),‖prefixMap u w‖^3 ∂wiener=(Real.sqrt (u:ℝ))^3*normCubeMean := by
  rw [←integral_map (f:=fun w : C(Time,ℝ) ↦ ‖w‖^3) (prefixMap u).continuous.measurable.aemeasurable (by fun_prop),prefix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul,normCubeMean]

lemma cube_add_le {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : (a+b)^3≤4*(a^3+b^3) := by
  have hh : 0≤(a+b)*(a-b)^2 := mul_nonneg (add_nonneg ha hb) (sq_nonneg _)
  nlinarith

lemma prefix_center_norm (u : Time) (w : C(Time,ℝ)) :
    ‖prefixMap u (centerMap w)‖ ≤ ‖prefixMap u w‖+(u:ℝ)*‖w‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (mul_nonneg u.property.1 (norm_nonneg _)))).mpr
  intro s
  simp only [prefixMap_apply,centerMap_apply]
  calc
    ‖w (prefixTime u s)-((prefixTime u s:Time):ℝ)*w 1‖ ≤ ‖w (prefixTime u s)‖+‖((prefixTime u s:Time):ℝ)*w 1‖ := norm_sub_le _ _
    _ ≤ ‖prefixMap u w‖+(u:ℝ)*‖w‖ := by
      apply add_le_add (ContinuousMap.norm_coe_le_norm (prefixMap u w) s)
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (prefixTime u s).property.1]
      apply mul_le_mul _ (ContinuousMap.norm_coe_le_norm w 1) (norm_nonneg _) u.property.1
      change (u:ℝ)*(s:ℝ)≤(u:ℝ)
      exact mul_le_of_le_one_right u.property.1 s.property.2

lemma prefix_bridge_normCube {u : Time} :
    ∫β : C(Time,ℝ),‖prefixMap u β‖^3 ∂bridgeLaw ≤ 8*(Real.sqrt (u:ℝ))^3*normCubeMean := by
  have hp : Integrable (fun w : C(Time,ℝ) ↦ ‖prefixMap u (centerMap w)‖^3) wiener :=
    ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp ((prefixMap u).comp centerMap)).integrable_norm_pow (by norm_num)
  have hq : Integrable (fun w : C(Time,ℝ) ↦ 4*(‖prefixMap u w‖^3+(u:ℝ)^3*‖w‖^3)) wiener :=
    ((prefix_normCube_integrable u).add (integrable_normCube.const_mul _)).const_mul _
  rw [bridgeLaw_center,integral_map centerMap.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫w : C(Time,ℝ),4*(‖prefixMap u w‖^3+(u:ℝ)^3*‖w‖^3) ∂wiener := by
      apply integral_mono hp hq
      intro w
      exact (pow_le_pow_left₀ (norm_nonneg _) (prefix_center_norm u w) 3).trans
        (by simpa only [mul_pow] using cube_add_le (norm_nonneg (prefixMap u w)) (mul_nonneg u.property.1 (norm_nonneg w)))
    _ = 4*((Real.sqrt (u:ℝ))^3*normCubeMean+(u:ℝ)^3*normCubeMean) := by
      rw [integral_const_mul,integral_add (prefix_normCube_integrable u) (integrable_normCube.const_mul _),
        integral_const_mul,prefix_normCube]
      rfl
    _ ≤ _ := by
      have hu : (u:ℝ) ≤ Real.sqrt (u:ℝ) := by
        apply Real.le_sqrt_of_sq_le
        simpa only [pow_two] using mul_le_of_le_one_right u.property.1 u.property.2
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ u.property.1 hu 3) normCubeMean_nonneg
      linarith

end HardSphere.Wiener

end

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def prefixSize (u : Time) (β : Noise) : ℝ := ∑j,‖prefixMap u (β j)‖
lemma prefixSize_nonneg (u : Time) (β : Noise) : 0≤prefixSize u β := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma prefixSize_continuous (u : Time) : Continuous (prefixSize u) := by unfold prefixSize; fun_prop
lemma prefixSize_smul (u : Time) (c : ℝ) (β : Noise) :
    prefixSize u (fun j ↦ c • β j)=|c| *prefixSize u β := by
  simp only [prefixSize,map_smul,norm_smul,Real.norm_eq_abs,Finset.mul_sum]
lemma prefixSize_memLp (u : Time) : MemLp (prefixSize u) 3 law := by
  apply memLp_finsetSum
  intro j hj
  have h := ((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (prefixMap u)).norm
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)

lemma sum_three_cube (f : Fin 3 → ℝ) (hf : ∀j,0≤f j) : (∑j,f j)^3≤16*(∑j,f j^3) := by
  have h := cube_add_le (add_nonneg (hf 0) (hf 1)) (hf 2)
  have h' := cube_add_le (hf 0) (hf 1)
  simp only [Fin.sum_univ_three]
  nlinarith [pow_nonneg (hf 2) 3]

lemma prefixSize_cube_integrable (u : Time) : Integrable (fun β ↦ (prefixSize u β)^3) law := by
  simpa only [Real.norm_eq_abs,abs_of_nonneg (prefixSize_nonneg u _)] using
    (prefixSize_memLp u).integrable_norm_pow (by norm_num : (3:ℕ)≠0)

lemma prefixSize_cube_mean (u : Time) :
    ∫β,(prefixSize u β)^3 ∂law ≤ 384*(Real.sqrt (u:ℝ))^3*normCubeMean := by
  have hi j : Integrable (fun β : Noise ↦ ‖prefixMap u (β j)‖^3) law := by
    exact (((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (prefixMap u)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  calc
    _ ≤ ∫β,16*(∑j,‖prefixMap u (β j)‖^3) ∂law := by
      apply integral_mono (prefixSize_cube_integrable u) ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul _)
      intro β
      exact sum_three_cube _ (fun j ↦ norm_nonneg _)
    _ = 16*(∑j : Fin 3,∫β : C(Time,ℝ),‖prefixMap u β‖^3 ∂bridgeLaw) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ ↦ hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hm := measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable (show Continuous (fun β : C(Time,ℝ) ↦ ‖prefixMap u β‖^3) from (prefixMap u).continuous.norm.pow 3).aestronglyMeasurable]
      rfl
    _ ≤ 16*(∑_j : Fin 3,8*(Real.sqrt (u:ℝ))^3*normCubeMean) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ ↦ prefix_bridge_normCube)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma remainder_prefix_memLp (s u : Time) : MemLp (prefixSize u) 3 (law.map (remainder s)) := by
  have hm : MemLp (fun β ↦ Real.sqrt (1-(s:ℝ))*prefixSize u β) 3 law := (prefixSize_memLp u).const_mul _
  rw [remainder_law]
  apply (memLp_map_measure_iff (g:=prefixSize u) (prefixSize_continuous u).aestronglyMeasurable
    (show Measurable (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j) from by fun_prop).aemeasurable).mpr
  simpa only [Function.comp_def,prefixSize_smul,abs_of_nonneg (Real.sqrt_nonneg _)] using hm

lemma remainder_prefix_mean (s u : Time) :
    ∫β,(prefixSize u β)^3 ∂law.map (remainder s) ≤
      384*(Real.sqrt (1-(s:ℝ)))^3*(Real.sqrt (u:ℝ))^3*normCubeMean := by
  rw [remainder_law,integral_map
    (show Measurable (fun β : Noise ↦ fun j ↦ Real.sqrt (1-(s:ℝ)) • β j) from by fun_prop).aemeasurable
    (show Continuous (fun β : Noise ↦ (prefixSize u β)^3) from (prefixSize_continuous u).pow 3).aestronglyMeasurable]
  simp only [prefixSize_smul,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul]
  have hh:=mul_le_mul_of_nonneg_left (prefixSize_cube_mean u) (show 0≤(Real.sqrt (1-(s:ℝ)))^3 by positivity)
  calc
    _ ≤ _ := hh
    _ = _ := by ring

end HardSphere.Bridge

end

end OAI
