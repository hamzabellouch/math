import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.LargePieces
import OAI.Geometry.CAT0Fillings.Differentiation.Parallelogram

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
lemma ae_restrict_of_arbitrarily_large_pieces
    {A : Type*} [MeasurableSpace A] (μ : Measure A) {s : Set A} (hs : MeasurableSet s)
    {P : A → Prop}
    (H : ∀ ε : ℝ, 0 < ε → ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ᵐ x ∂μ.restrict t, P x) :
    ∀ᵐ x ∂μ.restrict s, P x := by
  apply (ae_restrict_iff' hs).2
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨t,_,ht,htμ,hP⟩ := H ε hε
  have hnull : μ {x | ¬(x ∈ t → P x)} = 0 := ae_iff.1 ((ae_restrict_iff' ht).1 hP)
  calc μ {x | ¬(x ∈ s → P x)} ≤ μ ((s \ t) ∪ {x | ¬(x ∈ t → P x)}) := by
        apply measure_mono
        intro x hx
        simp only [mem_ofPred_eq, Classical.not_imp] at hx
        by_cases hxt : x ∈ t
        · exact Or.inr (by simpa only [mem_ofPred_eq, Classical.not_imp] using And.intro hxt hx.2)
        · exact Or.inl ⟨hx.1,hxt⟩
    _ ≤ μ (s \ t) + μ {x | ¬(x ∈ t → P x)} := measure_union_le _ _
    _ ≤ 0+(ε : ENNReal) := by simpa only [hnull,add_zero,zero_add,ENNReal.ofReal_coe_nnreal] using htμ
end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_parallelogram_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2) :
    ∀ᵐ x ∂μ.restrict s, ∀ u v : E,
      metricSeminorm f x (u+v)^2+metricSeminorm f x (u-v)^2 =
        2*metricSeminorm f x u^2+2*metricSeminorm f x v^2 := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd u v
  exact (hD x hx).parallelogram_of_quadrilateralOn μ
    (fun a ha b hb c hc d hd => hQ a (hts ha) b (hts hb) c (hts hc) d (hts hd)) hxd u v
end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_distance_bound_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) :
    ∀ᵐ x ∂μ.restrict s, ∀ w : E, A * ‖w‖ ≤ B * metricSeminorm f x w := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd w
  exact (hD x hx).distance_bound μ hxd
    (fun a ha b hb => hAB a (hts ha) b (hts hb)) w
end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

def HasCenteredMetricDifferentialWithin (s : Set E) (f : s → X)
    (p : Seminorm ℝ E) (x : s) : Prop :=
  (fun y : s => dist (f y) (f x) - p ((y : E)-(x : E))) =o[𝓝 x]
    (fun y : s => (y : E)-(x : E))

theorem exists_hilbertian_chart_differential
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2) :
    ∃ p : E → Seminorm ℝ E,
      (∀ v, Measurable (fun x => p x v)) ∧
      (∀ x, LipschitzWith K (p x)) ∧
      ∀ᵐ x ∂μ.restrict s, (∀ hx : x ∈ s,
        HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
        (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) ∧
        (∀ v, ‖v‖ ≤ (J : ℝ)*p x v) := by
  classical
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    exact hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  have hQG : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (G a) (G c)^2+dist (G b) (G d)^2 ≤
        dist (G a) (G b)^2+dist (G b) (G c)^2+dist (G c) (G d)^2+dist (G d) (G a)^2 := by
    intro a ha b hb c hc d hd
    simpa only [← hdist] using hQ ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
  have hJG : ∀ a ∈ s, ∀ b ∈ s, (1 : ℝ)*dist a b ≤ (J : ℝ)*dist (G a) (G b) := by
    intro a ha b hb
    have hh := hJ.le_mul_dist ⟨a,ha⟩ ⟨b,hb⟩
    change dist a b ≤ (J : ℝ)*dist (f ⟨a,ha⟩) (f ⟨b,hb⟩) at hh
    simpa only [←hdist,one_mul] using hh
  refine ⟨metricSeminorm G,fun v => measurable_metricSeminorm_apply hG v,
    fun x => metricSeminorm_lipschitz hG x,?_⟩
  have hdiff := (ae_hasCenteredMetricDifferential μ hG).filter_mono
    (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))
  filter_upwards [hdiff, ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG,
    ae_metricSeminorm_distance_bound_on μ hG hs hsf hJG] with x hdx hpx hjx
  refine ⟨?_,hpx,by simpa only [one_mul] using hjx⟩
  intro hx
  have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hx⟩ : s)) (𝓝 x) :=
    continuous_subtype_val.tendsto _
  have hr := hdx.comp_tendsto hc
  change (fun y : s => dist (G (y : E)) (G ((⟨x,hx⟩ : s) : E)) -
    metricSeminorm G x ((y : E)-x)) =o[𝓝 (⟨x,hx⟩ : s)] (fun y : s => (y : E)-x) at hr
  have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hx⟩) := hdist y ⟨x,hx⟩
  simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
end CAT0Fillings.MetricDifferentiation

end

end OAI
