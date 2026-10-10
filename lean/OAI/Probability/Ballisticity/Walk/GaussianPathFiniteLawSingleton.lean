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
namespace DirectionalTransience

lemma gaussianPathFiniteLaw_singleton (T : ℝ) (t : unitInterval) :
    (gaussianPathFiniteLaw T {t}).map (fun x => x ⟨t,by simp⟩) =
      gaussianReal 0 (Real.toNNReal (T*(t:ℝ))) := by
  let I : Finset unitInterval := {t}
  let z : Fin I.card := ⟨0,by simp [I]⟩
  have hj (j : Fin I.card) : j = z := by apply Fin.ext; have := j.isLt; simp [I] at this; omega
  have htimes0 (j : Fin I.card) : orderedTimes I j.castSucc = 0 := by
    rw [hj j]
    simp [orderedTimes,z]
  have htimes1 (j : Fin I.card) : orderedTimes I j.succ = t := by
    rw [orderedTimes_succ]
    exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem I rfl j)
  have hc (x : Fin I.card → ℝ) : incrementCumsum I x ⟨t,by simp [I]⟩ = x z := by
    simp only [incrementCumsum,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk]
    rw [show Finset.Iic ((I.orderIsoOfFin rfl).symm ⟨t,by simp [I]⟩) = {z} by
      ext j; simp only [Finset.mem_Iic,Finset.mem_singleton]; rw [hj j,hj ((I.orderIsoOfFin rfl).symm _)]; simp]
    simp
  change (gaussianPathFiniteLaw T I).map _ = _
  unfold gaussianPathFiniteLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : I → ℝ => x ⟨t,by simp [I]⟩) ∘ incrementCumsum I =
      (fun x : Fin I.card → ℝ => x z) := funext hc
  rw [he]
  have hm := (measurePreserving_eval (fun j : Fin I.card => gaussianReal 0
    (Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc)))) z).map_eq
  rw [hm,htimes0,htimes1]
  simp

lemma wiener_path_eval (W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (t : unitInterval) :
    (W : Measure C(unitInterval,ℝ)).map (fun g => g t) = gaussianReal 0 (Real.toNNReal (T*(t:ℝ))) := by
  rw [← gaussianPathFiniteLaw_singleton T t,← hW {t},Measure.map_map (by fun_prop) (continuous_path_restrict {t}).measurable]
  rfl

lemma height_path_gaussian_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
    (hF : ∀ h, Measurable (F h)) (r n : ℕ → ℝ) (hn : ∀ i, 0 < n i)
    (T : ℝ) (hT : 0 < T) (V : ℝ) (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim : TendstoInDistribution (fun i x => heightPolygon (fun h => F h x) (r i) (n i) T)
      atTop id (fun _ => μ) W)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T*V) I)
    (k : ℕ → ℕ) (hkn : ∀ i, (k i : ℝ) ≤ T*n i) {s : ℝ}
    (hs : Tendsto (fun i => (k i : ℝ)/n i) atTop (𝓝 s)) :
    TendstoInDistribution (fun i x => F (k i) x/r i) atTop id (fun _ => μ)
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
    ⟨μ.map (fun x => heightPolygon (fun h => F h x) (r i) (n i) T),
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
  refine ⟨fun i => ((hF (k i)).div_const _).aemeasurable,measurable_id.aemeasurable,?_⟩
  have he (i : ℕ) : (P i).map (fun path => path (t i)) =
      (⟨μ.map (fun x => F (k i) x/r i),inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change (μ.map (fun x => heightPolygon (fun h => F h x) (r i) (n i) T)).map (fun g => g (t i)) = _
    rw [Measure.map_map (continuous_eval_const (t i)).measurable (measurable_heightPolygon F hF _ _ _)]
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
