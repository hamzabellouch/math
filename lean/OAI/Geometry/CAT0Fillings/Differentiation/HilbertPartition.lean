import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.HilbertCharts
import OAI.Geometry.CAT0Fillings.Differentiation.Partitions

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
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
theorem exists_ae_nearIsometric_partition_with_property
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {P : E → Prop} (hP : ∀ᵐ x ∂μ.restrict s, P x)
    {A : ℝ} (hA : 0 < A)
    (hbound : ∀ x ∈ s, P x → ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s ∧ P (c i)) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  have hnull : μ {x | ¬(x ∈ s → P x)} = 0 :=
    ae_iff.mp ((ae_restrict_iff' hs).mp hP)
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null hnull
  let s₀ := s \ N
  have hs₀ : MeasurableSet s₀ := hs.diff hNm
  have hprop : ∀ x ∈ s₀, P x := by
    intro x hx
    by_contra hp
    exact hx.2 (hN (by simpa using And.intro hx.1 hp))
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition μ hf hs₀
      ((measure_mono sdiff_subset).trans_lt hsf.lt_top).ne hA
      (fun x hx => hbound x hx.1 (hprop x hx)) hε
  refine ⟨c,t,htm,fun i => (hts i).trans sdiff_subset,hdisj,?_,?_,hineq⟩
  · apply le_antisymm _ bot_le
    calc μ (s \ ⋃ i, t i) ≤ μ (N ∪ (s₀ \ ⋃ i, t i)) := by
          apply measure_mono
          intro x hx
          by_cases hn : x ∈ N
          · exact Or.inl hn
          · exact Or.inr ⟨⟨hx.1,hn⟩,hx.2⟩
      _ ≤ μ N + μ (s₀ \ ⋃ i, t i) := measure_union_le _ _
      _ = 0 := by rw [hN0,ht0,add_zero]
  · intro i hi
    exact ⟨(hcs i hi).1,hprop _ (hcs i hi)⟩

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

theorem exists_hilbertian_nearIsometric_chart_partition
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : ℕ → Seminorm ℝ E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, LipschitzWith K (p i)) ∧
      (∀ i, (t i).Nonempty →
        (∀ u v, p i (u+v)^2+p i (u-v)^2 = 2*p i u^2+2*p i v^2) ∧
        (∀ v, ‖v‖ ≤ (J : ℝ)*p i v)) ∧
      ∀ i, ∀ y : s, (y : E) ∈ t i → ∀ z : s, (z : E) ∈ t i →
        (1-ε)*p i ((y : E)-(z : E)) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*p i ((y : E)-(z : E)) := by
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
  let P : E → Prop := fun x =>
    (∀ u v, metricSeminorm G x (u+v)^2+metricSeminorm G x (u-v)^2 =
      2*metricSeminorm G x u^2+2*metricSeminorm G x v^2) ∧
    (∀ v, ‖v‖ ≤ (J : ℝ)*metricSeminorm G x v)
  have hP : ∀ᵐ x ∂μ.restrict s, P x := by
    filter_upwards [ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG,
      ae_metricSeminorm_distance_bound_on μ hG hs hsf hJG] with x hx hj
    exact ⟨hx,by simpa only [one_mul] using hj⟩
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition_with_property μ hG hs hsf hP
      (A := (J : ℝ)+1) (by positivity)
      (fun x _ hx v => (hx.2 v).trans <| mul_le_mul_of_nonneg_right
        (by linarith) (apply_nonneg (metricSeminorm G x) v)) hε
  refine ⟨fun i => metricSeminorm G (c i),t,htm,hts,hdisj,ht0,
    fun i => metricSeminorm_lipschitz hG (c i),fun i hi => (hcs i hi).2,?_⟩
  intro i y hy z hz
  simpa only [hdist] using hineq i y hy z hz
end CAT0Fillings.MetricDifferentiation

end

end OAI
