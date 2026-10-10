import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightIncrement
import OAI.Probability.Ballisticity.Estimates.GridLinear

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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def heightPolygon (F : ℕ → ℝ) (r n T : ℝ) : C(unitInterval,ℝ) :=
  ContinuousMap.const _ (F 0/r) + scaledPolygon (heightIncrement F) r n T

lemma measurable_heightPolygon {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T : ℝ) :
    Measurable (fun ω => heightPolygon (fun k => F k ω) r n T) := by
  exact (ContinuousMap.continuous_const'.measurable.comp ((hF 0).div_const _)).add
    (measurable_scaledPolygon _ (measurable_heightIncrement F hF) _ _ _)

lemma heightPolygon_formula (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n) (t : unitInterval) :
    heightPolygon F r n T t =
      (F ⌊T*n*(t:ℝ)⌋₊ + (T*n*(t:ℝ)-⌊T*n*(t:ℝ)⌋₊)*
        (F (⌊T*n*(t:ℝ)⌋₊+1)-F ⌊T*n*(t:ℝ)⌋₊))/r := by
  have ht : 0 ≤ T*n*(t:ℝ) := mul_nonneg h t.2.1
  have hN : ⌊T*n*(t:ℝ)⌋₊ < ⌊T*n⌋₊+1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right h t.2.2))
  simp only [heightPolygon,ContinuousMap.add_apply,ContinuousMap.const_apply,scaledPolygon_apply,
    linearPolygon_formula _ _ ht hN,realPartialSum_heightIncrement,heightIncrement]
  ring

lemma heightPolygon_grid (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n)
    (j : ℕ) (t : unitInterval) (ht : T*n*(t:ℝ) = j) :
    heightPolygon F r n T t = F j/r := by
  rw [heightPolygon_formula F r n T h,ht]
  simp

lemma realPartialSum_sub (x y : ℕ → ℝ) (j : ℕ) :
    realPartialSum (fun k => x k-y k) j = realPartialSum x j-realPartialSum y j := by
  simp [realPartialSum,Finset.sum_sub_distrib]

lemma scaledPolygon_sub (x y : ℕ → ℝ) (r n T : ℝ) :
    scaledPolygon (fun k => x k-y k) r n T = scaledPolygon x r n T-scaledPolygon y r n T := by
  ext t
  simp only [scaledPolygon_apply,ContinuousMap.sub_apply,linearPolygon,mul_sub,Finset.sum_sub_distrib,sub_div]

lemma heightPolygon_sub (F G : ℕ → ℝ) (r n T : ℝ) :
    heightPolygon (fun k => F k-G k) r n T = heightPolygon F r n T-heightPolygon G r n T := by
  have he : heightIncrement (fun k => F k-G k) = fun k => heightIncrement F k-heightIncrement G k := by
    funext k
    simp only [heightIncrement]
    ring
  ext t
  simp only [heightPolygon,he,scaledPolygon_sub,sub_div,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,ContinuousMap.const_apply]
  ring

lemma heightPolygon_segment (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n)
    (j : ℕ) (t : unitInterval) (hjt : (j:ℝ) ≤ T*n*(t:ℝ)) (htj : T*n*(t:ℝ) ≤ (j:ℝ)+1) :
    heightPolygon F r n T t =
      (F j+(T*n*(t:ℝ)-j)*(F (j+1)-F j))/r := by
  by_cases he : T*n*(t:ℝ) = (j:ℝ)+1
  · rw [heightPolygon_grid F r n T h (j+1) t (by simpa using he),he]
    congr 1
    ring
  · have hj : ⌊T*n*(t:ℝ)⌋₊ = j := Nat.floor_eq_iff (mul_nonneg h t.2.1) |>.mpr ⟨hjt,lt_of_le_of_ne htj he⟩
    rw [heightPolygon_formula F r n T h,hj]

lemma heightPolygon_gridLinear (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n) :
    GridLinear (T*n) (heightPolygon F r n T) := by
  intro j u v t hu hv htu htv
  have hjt : (j:ℝ) ≤ T*n*(t:ℝ) := hu ▸ mul_le_mul_of_nonneg_left htu h
  have htj : T*n*(t:ℝ) ≤ (j:ℝ)+1 := hv ▸ mul_le_mul_of_nonneg_left htv h
  rw [heightPolygon_segment F r n T h j t hjt htj,
    heightPolygon_grid F r n T h j u hu,
    heightPolygon_grid F r n T h (j+1) v (by simpa using hv)]
  ring

lemma heightPolygon_restrict (F : ℕ → ℝ) (r n T S : ℝ) (hn : 0 ≤ n)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (a : unitInterval) (ha : S*(a:ℝ) = T) :
    pathRestrictScale a (heightPolygon F r n S) = heightPolygon F r n T := by
  ext t
  rw [pathRestrictScale_apply,heightPolygon_formula F r n S (mul_nonneg hS hn),
    heightPolygon_formula F r n T (mul_nonneg hT hn)]
  have he : S*n*((a*t:unitInterval):ℝ) = T*n*(t:ℝ) := by
    change S*n*((a:ℝ)*(t:ℝ)) = T*n*(t:ℝ)
    rw [← ha]
    ring
  rw [he]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
