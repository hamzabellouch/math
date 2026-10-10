import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightPolygon

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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
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

lemma norm_heightPolygon_le (F : ℕ → ℝ) (r n T : ℝ) (hq : 0 ≤ T*n)
    {E : ℝ} (hE : 0 ≤ E) (hb : ∀ j ≤ ⌊T*n⌋₊+1, |F j/r| ≤ E) :
    ‖heightPolygon F r n T‖ ≤ E := by
  apply (ContinuousMap.norm_le _ hE).mpr
  intro t
  rw [Real.norm_eq_abs,heightPolygon_formula F r n T hq t]
  let u := T*n*(t:ℝ)
  let j := ⌊u⌋₊
  have hu : 0 ≤ u := mul_nonneg hq t.2.1
  have hv0 : 0 ≤ u-(j:ℝ) := sub_nonneg.mpr (Nat.floor_le hu)
  have hv1 : u-(j:ℝ) ≤ 1 := by have := Nat.lt_floor_add_one u; change u < (j:ℝ)+1 at this; linarith
  have hj : j ≤ ⌊T*n⌋₊ := Nat.floor_mono (mul_le_of_le_one_right hq t.2.2)
  have he : (F j+(u-j)*(F (j+1)-F j))/r = (1-(u-j))*(F j/r)+(u-j)*(F (j+1)/r) := by ring
  change |(F j+(u-j)*(F (j+1)-F j))/r| ≤ E
  rw [he]
  calc
    _ ≤ |(1-(u-j))*(F j/r)|+|(u-j)*(F (j+1)/r)| := abs_add_le _ _
    _ = (1-(u-j))*|F j/r|+(u-j)*|F (j+1)/r| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hv1),abs_of_nonneg hv0]
    _ ≤ (1-(u-j))*E+(u-j)*E := by
      gcongr
      · exact hb j (by omega)
      · exact hb (j+1) (by omega)
    _ = E := by ring

lemma heightPolygon_tendsto_zero_of_grid (F : ℕ → ℕ → ℝ) (r n : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ ε > 0, ∀ᶠ i in atTop, ∀ j : ℕ, (j:ℝ) ≤ (T+1)*n i → |F i j/r i| < ε) :
    Tendsto (fun i => heightPolygon (F i) (r i) (n i) T) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hb (ε/2) (half_pos hε),hn.eventually (eventually_ge_atTop (1:ℝ))] with i hi hni
  rw [dist_zero_right]
  apply lt_of_le_of_lt (norm_heightPolygon_le _ _ _ _ (mul_nonneg hT (by positivity)) (half_pos hε).le _) (half_lt_self hε)
  intro j hj
  have hjr : (j:ℝ) ≤ (⌊T*n i⌋₊:ℝ)+1 := by exact_mod_cast hj
  have hfl := Nat.floor_le (mul_nonneg hT (show 0 ≤ n i by positivity))
  exact (hi j (by nlinarith)).le

lemma heightPolygon_change_center (F b c : ℕ → ℝ) (r n T : ℝ) :
    heightPolygon (fun h => F h-c h) r n T-heightPolygon (fun h => F h-b h) r n T =
      heightPolygon (fun h => b h-c h) r n T := by
  rw [← heightPolygon_sub]
  congr 1
  funext h
  ring

theorem height_path_change_center {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ) (hF : ∀ h, Measurable (F h))
    (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (r n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ ε > 0, ∀ᶠ i in atTop, ∀ j : ℕ, (j:ℝ) ≤ (T+1)*n i → |(b j-c i j)/r i| < ε)
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim : TendstoInDistribution (fun i x => heightPolygon (fun h => F h x-b h) (r i) (n i) T)
      atTop id (fun _ => μ) W) :
    TendstoInDistribution (fun i x => heightPolygon (fun h => F h x-c i h) (r i) (n i) T)
      atTop id (fun _ => μ) W := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hlim
  · have hh := heightPolygon_tendsto_zero_of_grid (fun i j => b j-c i j) r n hn T hT hb
    apply tendstoInMeasure_of_tendsto_ae
    · intro i
      have he : (fun x => heightPolygon (fun h => F h x-c i h) (r i) (n i) T) -
          (fun x => heightPolygon (fun h => F h x-b h) (r i) (n i) T) =
          (fun _ => heightPolygon (fun h => b h-c i h) (r i) (n i) T) := by
        funext x
        exact heightPolygon_change_center _ _ _ _ _ _
      change AEStronglyMeasurable ((fun x => heightPolygon (fun h => F h x-c i h) (r i) (n i) T) -
        (fun x => heightPolygon (fun h => F h x-b h) (r i) (n i) T)) μ
      rw [he]
      exact aestronglyMeasurable_const
    · exact Eventually.of_forall (fun x => by simpa only [Pi.sub_apply,heightPolygon_change_center,Pi.zero_apply] using hh)
  · intro i
    exact (measurable_heightPolygon _ (fun h => (hF h).sub_const _) _ _ _).aemeasurable

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
