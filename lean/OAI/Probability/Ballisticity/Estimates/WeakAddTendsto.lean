import Mathlib
import OAI.Probability.Ballisticity.Estimates.DominatedTranslationBounded
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
namespace DirectionalTransience

lemma weak_add_tendsto {μ ν : ℕ → ProbabilityMeasure ℝ} {M N : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 M)) (hν : Tendsto ν atTop (𝓝 N)) :
    Tendsto (fun i => ((μ i).prod (ν i)).map
      (fun pair => pair.1 + pair.2)) atTop
      (𝓝 ((M.prod N).map (fun pair => pair.1 + pair.2))) := by
  exact (ProbabilityMeasure.continuous_map (continuous_fst.add continuous_snd)).tendsto
    (M.prod N) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (M,N) |>.comp (hμ.prodMk_nhds hν))

lemma gaussian_prod_add (v w : ℝ≥0) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)).map (fun p : ℝ × ℝ => p.1+p.2) =
      gaussianReal 0 (v+w) := by
  simpa only [Measure.conv,zero_add] using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := v) (v₂ := w))

lemma centered_height_additive_sequence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
    (hF : ∀ h, Measurable (F h)) (b : ℕ → ℝ) (r n : ℕ → ℝ)
    (hn : ∀ i, 0 < n i) (T V : ℝ) (hT : 0 < T) (hV : 0 ≤ V)
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim : TendstoInDistribution (fun i x => heightPolygon (fun h => F h x-b h) (r i) (n i) T)
      atTop id (fun _ => μ) W)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T*V) I)
    (p : ℝ) (hp : 0 < p)
    (hd : ∀ k j : ℕ, 0 < k → 0 < j →
      ENNReal.ofReal p • (μ.prod μ).map (fun P => F k P.1+F j P.2) ≤ μ.map (F (k+j)))
    (k j : ℕ → ℕ) (hk : ∀ i, 0 < k i) (hj : ∀ i, 0 < j i)
    (hkn : ∀ i, ((k i+j i : ℕ) : ℝ) ≤ T*n i)
    {s t : ℝ} (hs : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 s))
    (ht : Tendsto (fun i => (j i:ℝ)/n i) atTop (𝓝 t)) :
    Tendsto (fun i => (b (k i+j i)-b (k i)-b (j i))/r i) atTop (𝓝 0) := by
  let G := fun h x => F h x-b h
  have hG (h : ℕ) : Measurable (G h) := (hF h).sub_const _
  have hs0 : 0 ≤ s := le_of_tendsto_of_tendsto tendsto_const_nhds hs
    (Eventually.of_forall fun i => div_nonneg (Nat.cast_nonneg _) (hn i).le)
  have ht0 : 0 ≤ t := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall fun i => div_nonneg (Nat.cast_nonneg _) (hn i).le)
  have hkbound (i : ℕ) : (k i:ℝ) ≤ T*n i := le_trans (by exact_mod_cast Nat.le_add_right (k i) (j i)) (hkn i)
  have hjbound (i : ℕ) : (j i:ℝ) ≤ T*n i := le_trans (by exact_mod_cast Nat.le_add_left (j i) (k i)) (hkn i)
  have hks := height_path_gaussian_eval μ G hG r n hn T hT V W hlim hW k hkbound hs
  have hjs := height_path_gaussian_eval μ G hG r n hn T hT V W hlim hW j hjbound ht
  have hksj := height_path_gaussian_eval μ G hG r n hn T hT V W hlim hW
    (fun i => k i+j i) hkn (show Tendsto (fun i => ((k i+j i:ℕ):ℝ)/n i) atTop (𝓝 (s+t)) by
      simpa only [Nat.cast_add,add_div] using hs.add ht)
  let A : ℕ → ProbabilityMeasure ℝ := fun i => ⟨μ.map (fun x => G (k i) x/r i),
    inferInstance⟩
  let B : ℕ → ProbabilityMeasure ℝ := fun i => ⟨μ.map (fun x => G (j i) x/r i),
    inferInstance⟩
  let C : ℕ → ProbabilityMeasure ℝ := fun i => ⟨μ.map (fun x => G (k i+j i) x/r i),
    inferInstance⟩
  have hA : Tendsto A atTop (𝓝 ⟨gaussianReal 0 (Real.toNNReal (V*s)),inferInstance⟩) := by
    simpa only [Measure.map_id] using hks.tendsto
  have hB : Tendsto B atTop (𝓝 ⟨gaussianReal 0 (Real.toNNReal (V*t)),inferInstance⟩) := by
    simpa only [Measure.map_id] using hjs.tendsto
  have hC : Tendsto C atTop (𝓝 ⟨gaussianReal 0 (Real.toNNReal (V*(s+t))),inferInstance⟩) := by
    simpa only [Measure.map_id] using hksj.tendsto
  let D : ℕ → ProbabilityMeasure ℝ := fun i => ((A i).prod (B i)).map
    (fun pair => pair.1 + pair.2)
  have hvar : Real.toNNReal (V*s)+Real.toNNReal (V*t) = Real.toNNReal (V*(s+t)) := by
    rw [← Real.toNNReal_add (mul_nonneg hV hs0) (mul_nonneg hV ht0),mul_add]
  have hD : Tendsto D atTop (𝓝 ⟨gaussianReal 0 (Real.toNNReal (V*(s+t))),inferInstance⟩) := by
    have hh := weak_add_tendsto hA hB
    have he : ProbabilityMeasure.map (ProbabilityMeasure.prod
        (⟨gaussianReal 0 (Real.toNNReal (V*s)),inferInstance⟩ : ProbabilityMeasure ℝ)
        (⟨gaussianReal 0 (Real.toNNReal (V*t)),inferInstance⟩ : ProbabilityMeasure ℝ))
          (fun pair => pair.1 + pair.2) =
        (⟨gaussianReal 0 (Real.toNNReal (V*(s+t))),inferInstance⟩ : ProbabilityMeasure ℝ) := by
      apply Subtype.ext
      exact (gaussian_prod_add _ _).trans (congrArg (gaussianReal 0) hvar)
    rw [he] at hh
    exact hh
  apply weak_gaussian_domination_center _ hD hC hp
  intro i
  let a := fun x : ℝ => (x-b (k i+j i))/r i
  have ha : Measurable a := by fun_prop
  have hh := Measure.map_mono (hd (k i) (j i) (hk i) (hj i)) ha
  have hsum : Measurable (fun P : Ω × Ω => F (k i) P.1+F (j i) P.2) :=
    ((hF (k i)).comp measurable_fst).add ((hF (j i)).comp measurable_snd)
  rw [Measure.map_smul _ ha.aemeasurable,Measure.map_map ha hsum,
    Measure.map_map ha (hF (k i+j i))] at hh
  have he : (D i : Measure ℝ).map (fun x => x-(b (k i+j i)-b (k i)-b (j i))/r i) =
      (μ.prod μ).map (a ∘ (fun P => F (k i) P.1+F (j i) P.2)) := by
    change (((μ.map _).prod (μ.map _)).map _).map _ = _
    rw [Measure.map_prod_map _ _ ((hG _).div_const _) ((hG _).div_const _),
      Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext P
    dsimp [G,a]
    ring
  rw [he]
  exact hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
