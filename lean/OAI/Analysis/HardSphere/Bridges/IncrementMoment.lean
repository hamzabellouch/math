import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeNoise

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def incrementMap (s u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) := (prefixMap u).comp (suffixMap s)
@[simp] lemma incrementMap_apply (s u : Time) (f : C(Time,ℝ)) (q : Time) :
    incrementMap s u f q=f (suffixTime s (prefixTime u q))-f s := rfl
lemma suffix_wiener_law (s : Time) : wiener.map (suffixMap s)=wiener.map (fun β ↦ Real.sqrt (1-(s:ℝ)) • β) := by
  rw [wiener,Measure.map_map (suffixMap s).continuous.measurable measurable_path,
    Measure.map_map (by fun_prop) measurable_path]
  exact suffix_law s
lemma increment_wiener_mean (s u : Time) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^3 ∂wiener =
      (Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean := by
  change (∫β : C(Time,ℝ),‖prefixMap u (suffixMap s β)‖^3 ∂wiener)=_
  rw [←integral_map (f:=fun β : C(Time,ℝ) ↦ ‖prefixMap u β‖^3) (suffixMap s).continuous.measurable.aemeasurable (by fun_prop),suffix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul]
  rw [prefix_normCube,Real.sqrt_mul (sub_nonneg.mpr s.property.2),mul_pow]
  ring

lemma increment_center_norm (s u : Time) (f : C(Time,ℝ)) :
    ‖incrementMap s u (centerMap f)‖≤‖incrementMap s u f‖+((1-(s:ℝ))*(u:ℝ))*‖f‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1) (norm_nonneg _)))).mpr
  intro q
  have hs0 := sub_nonneg.mpr s.property.2
  have hu0 := u.property.1
  have hq0 := q.property.1
  have he : incrementMap s u (centerMap f) q=incrementMap s u f q-
      ((1-(s:ℝ))*(u:ℝ)*(q:ℝ))*f 1 := by
    simp only [incrementMap_apply,centerMap_apply]
    dsimp [suffixTime,prefixTime]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add (ContinuousMap.norm_coe_le_norm _ _)
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply mul_le_mul _ (ContinuousMap.norm_coe_le_norm f 1) (norm_nonneg _) (by positivity)
  exact mul_le_of_le_one_right (by positivity) q.property.2

lemma increment_bridge_mean (s u : Time) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^3 ∂bridgeLaw ≤
      8*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean := by
  let δ := (1-(s:ℝ))*(u:ℝ)
  have hd : 0≤δ := mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1
  have hd1 : δ≤1 := by dsimp [δ]; nlinarith [s.property.1,s.property.2,u.property.1,u.property.2]
  have hp : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u (centerMap f)‖^3) wiener :=
    ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp ((incrementMap s u).comp centerMap)).integrable_norm_pow (by norm_num)
  have hi : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u f‖^3) wiener :=
    ((IsGaussian.memLp_id wiener 3 (by norm_num)).continuousLinearMap_comp (incrementMap s u)).integrable_norm_pow (by norm_num)
  rw [bridgeLaw_center,integral_map centerMap.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫f : C(Time,ℝ),4*(‖incrementMap s u f‖^3+δ^3*‖f‖^3) ∂wiener := by
      apply integral_mono hp ((hi.add (integrable_normCube.const_mul _)).const_mul _)
      intro f
      exact (pow_le_pow_left₀ (norm_nonneg _) (increment_center_norm s u f) 3).trans
        (by simpa only [mul_pow,Pi.add_apply,δ] using cube_add_le (norm_nonneg (incrementMap s u f)) (mul_nonneg hd (norm_nonneg f)))
    _ = 4*((Real.sqrt δ)^3*normCubeMean+δ^3*normCubeMean) := by
      rw [integral_const_mul,integral_add hi (integrable_normCube.const_mul _),integral_const_mul,increment_wiener_mean]
      rfl
    _ ≤ _ := by
      have hds : δ≤Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hds 3) normCubeMean_nonneg
      change _ ≤ 8*(Real.sqrt δ)^3*normCubeMean
      linarith

end HardSphere.Wiener

namespace HardSphere.Bridge
open Wiener GaussianPacking

def incrementSize (s u : Time) (β : Noise) : ℝ := ∑j,‖incrementMap s u (β j)‖
lemma incrementSize_nonneg (s u : Time) (β : Noise) : 0 ≤ incrementSize s u β := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma incrementSize_continuous (s u : Time) : Continuous (incrementSize s u) := by unfold incrementSize; fun_prop
lemma incrementSize_smul (s u : Time) (c : ℝ) (β : Noise) :
    incrementSize s u (fun j ↦ c • β j)=|c| *incrementSize s u β := by
  simp only [incrementSize,map_smul,norm_smul,Real.norm_eq_abs,Finset.mul_sum]
lemma incrementSize_memLp (s u : Time) : MemLp (incrementSize s u) 3 law := by
  apply memLp_finsetSum
  intro j hj
  have h := ((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (incrementMap s u)).norm
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)

lemma incrementSize_cube_integrable (s u : Time) : Integrable (fun β ↦ (incrementSize s u β)^3) law := by
  simpa only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s u _)] using
    (incrementSize_memLp s u).integrable_norm_pow (by norm_num : (3:ℕ)≠0)

lemma incrementSize_cube_mean (s u : Time) :
    ∫β,(incrementSize s u β)^3 ∂law  ≤  384*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean := by
  have hi j : Integrable (fun β : Noise ↦ ‖incrementMap s u (β j)‖^3) law := by
    exact (((IsGaussian.memLp_id bridgeLaw 3 (by norm_num)).continuousLinearMap_comp (incrementMap s u)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)).integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  calc
    _  ≤  ∫β,16*(∑j,‖incrementMap s u (β j)‖^3) ∂law := by
      apply integral_mono (incrementSize_cube_integrable s u) ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul _)
      intro β
      exact sum_three_cube _ (fun j ↦ norm_nonneg _)
    _ = 16*(∑j : Fin 3,∫β : C(Time,ℝ),‖incrementMap s u β‖^3 ∂bridgeLaw) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ ↦ hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hm := measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable (show Continuous (fun β : C(Time,ℝ) ↦ ‖incrementMap s u β‖^3) from (incrementMap s u).continuous.norm.pow 3).aestronglyMeasurable]
      rfl
    _  ≤  16*(∑_j : Fin 3,8*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^3*normCubeMean) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ ↦ increment_bridge_mean s u)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

def incrementFluctuation (t r : ℝ) (s w : Time) (β : Noise) : ℝ := Real.sqrt (2*t)/r*incrementSize s w β
lemma incrementFluctuation_continuous (t r : ℝ) (s w : Time) : Continuous (incrementFluctuation t r s w) :=
  (incrementSize_continuous s w).const_mul _
lemma incrementFluctuation_nonneg {t r : ℝ} (hr : 0 ≤ r) (s w : Time) (β : Noise) : 0 ≤ incrementFluctuation t r s w β :=
  mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hr) (incrementSize_nonneg s w β)
lemma incrementFluctuation_memLp (t r : ℝ) (s w : Time) : MemLp (incrementFluctuation t r s w) 3 law :=
  (incrementSize_memLp s w).const_mul _

lemma incrementFluctuation_mean {t r : ℝ} (ht : 0 ≤ t) (hr : 0<r) (s w : Time)
    (hscale : t*(1-(s:ℝ))*(w:ℝ) ≤ r^2) :
    ∫β,(incrementFluctuation t r s w β)^3 ∂law  ≤  3072*normCubeMean := by
  let a := Real.sqrt (2*t)/r*Real.sqrt ((1-(s:ℝ))*(w:ℝ))
  have hd : 0 ≤ (1-(s:ℝ))*(w:ℝ) := mul_nonneg (sub_nonneg.mpr s.property.2) w.property.1
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a^2 ≤ 2 := by
    dsimp [a]
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hd,div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    convert mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 2) using 1
    ring
  have ha : a ≤ 2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left (incrementSize_cube_mean s w)
    (show 0 ≤ (Real.sqrt (2*t)/r)^3 by positivity)
  simp only [incrementFluctuation,mul_pow,integral_const_mul]
  calc
    _  ≤  _ := hb
    _ = 384*a^3*normCubeMean := by dsimp [a]; ring
    _  ≤  3072*normCubeMean := by
      have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 3) normCubeMean_nonneg
      nlinarith

lemma incrementFluctuation_eval {t r : ℝ} (hr : 0<r) (s w q : Time) (hq : (q:ℝ) ≤ (w:ℝ)) (β : Noise) (j : Fin 3) :
    |Real.sqrt (2*t)*(β j (suffixTime s q)-β j s)| ≤ r*incrementFluctuation t r s w β := by
  have hp : ‖β j (suffixTime s q)-β j s‖ ≤ incrementSize s w β := (prefix_norm_eval w q hq (suffixMap s (β j))).trans
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (incrementMap s w (β i))) (Finset.mem_univ j))
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : r*incrementFluctuation t r s w β=Real.sqrt (2*t)*incrementSize s w β := by unfold incrementFluctuation; field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)

end HardSphere.Bridge

end

end OAI
