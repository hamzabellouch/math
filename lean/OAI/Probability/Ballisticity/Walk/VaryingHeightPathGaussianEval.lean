import Mathlib
import OAI.Probability.Ballisticity.Walk.GaussianPathFiniteLawSingleton

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
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma varying_height_path_gaussian_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (F : ℕ → ℕ → Ω → ℝ)
    (hF : ∀ i h, Measurable (F i h)) (r n : ℕ → ℝ) (hn : ∀ i, 0 < n i)
    (T : ℝ) (hT : 0 < T) (V : ℝ) (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim : TendstoInDistribution (fun i x => heightPolygon (fun h => F i h x) (r i) (n i) T)
      atTop id μ W)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T*V) I)
    (k : ℕ → ℕ) (hkn : ∀ i, (k i : ℝ) ≤ T*n i) {s : ℝ}
    (hs : Tendsto (fun i => (k i : ℝ)/n i) atTop (𝓝 s)) :
    TendstoInDistribution (fun i x => F i (k i) x/r i) atTop id μ
      (gaussianReal 0 (Real.toNNReal (V*s))) := by
  have hs0 : 0 ≤ s := le_of_tendsto_of_tendsto tendsto_const_nhds hs
    (Eventually.of_forall fun i => div_nonneg (Nat.cast_nonneg _) (hn i).le)
  have hsT : s ≤ T := le_of_tendsto_of_tendsto hs tendsto_const_nhds
    (Eventually.of_forall fun i => (div_le_iff₀ (hn i)).mpr (hkn i))
  let t : ℕ → unitInterval := fun i => ⟨(k i:ℝ)/(T*n i),
    div_nonneg (Nat.cast_nonneg _) (mul_pos hT (hn i)).le,
    (div_le_one (mul_pos hT (hn i))).mpr (hkn i)⟩
  let u : unitInterval := ⟨s/T,div_nonneg hs0 hT.le,(div_le_one hT).mpr hsT⟩
  have ht : Tendsto t atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun i => (k i:ℝ)/(T*n i)) atTop (𝓝 (s/T))
    convert hs.div_const T using 1
    funext i
    ring
  let P : ℕ → ProbabilityMeasure C(unitInterval,ℝ) := fun i =>
    ⟨(μ i).map (fun x => heightPolygon (fun h => F i h x) (r i) (n i) T),
      inferInstance⟩
  have hP : Tendsto P atTop (𝓝 W) := by
    have hh := hlim.tendsto
    have hid : (⟨(W : Measure C(unitInterval,ℝ)).map id,
      inferInstance⟩ : ProbabilityMeasure C(unitInterval,ℝ)) = W :=
        Subtype.ext Measure.map_id
    rw [hid] at hh
    exact hh
  have hev := weak_path_eval_tendsto hP ht
  have hwm : W.map (fun path => path u) =
      (⟨gaussianReal 0 (Real.toNNReal (V*s)),inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change (W : Measure C(unitInterval,ℝ)).map (fun g => g u) = _
    rw [wiener_path_eval W (T*V) hW]
    congr 2
    change (T*V)*(s/T) = V*s
    field_simp
  rw [hwm] at hev
  refine ⟨fun i => ((hF i (k i)).div_const _).aemeasurable,measurable_id.aemeasurable,?_⟩
  have he (i : ℕ) : (P i).map (fun path => path (t i)) =
      (⟨(μ i).map (fun x => F i (k i) x/r i),inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change ((μ i).map (fun x => heightPolygon (fun h => F i h x) (r i) (n i) T)).map (fun g => g (t i)) = _
    rw [Measure.map_map (continuous_eval_const (t i)).measurable (measurable_heightPolygon (F i) (hF i) _ _ _)]
    congr 1
    funext x
    exact heightPolygon_grid _ _ _ _ (mul_pos hT (hn i)).le (k i) (t i)
      (by change T*n i*((k i:ℝ)/(T*n i)) = _; field_simp [hT.ne',(hn i).ne'])
  simpa only [he,Measure.map_id] using hev

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
