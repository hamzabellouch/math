import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

abbrev GraphAmbient := WithLp 2
  ((Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) × (Lp (Euc n) 2 q.atlasMeasure))

noncomputable def graphPoint {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) : q.GraphAmbient :=
  WithLp.toLp 2 (value hu,q.gradient hu)

lemma graphPoint_add {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    q.graphPoint (hu.add hv) = q.graphPoint hu+q.graphPoint hv := by
  change WithLp.toLp 2 (value (hu.add hv),q.gradient (hu.add hv)) = _
  rw [value_add hu hv,q.gradient_add hu hv]
  exact WithLp.toLp_add 2 (value hu,q.gradient hu) (value hv,q.gradient hv)

lemma graphPoint_smul {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (c : ℝ) :
    q.graphPoint ((lipschitzWith_smul c).comp hu) = c • q.graphPoint hu := by
  change WithLp.toLp 2 (value ((lipschitzWith_smul c).comp hu),q.gradient ((lipschitzWith_smul c).comp hu)) = _
  rw [value_smul hu c,q.gradient_smul hu c]
  exact WithLp.toLp_smul 2 c (value hu,q.gradient hu)

noncomputable def lipschitzGraph : Submodule ℝ q.GraphAmbient where
  carrier := {P | ∃ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u), P = q.graphPoint hu}
  zero_mem' := by
    refine ⟨fun x => (0:ℝ) • (0:ℝ),_,(lipschitzWith_smul (0:ℝ)).comp (LipschitzWith.const (0:ℝ)),?_⟩
    simpa only [zero_smul] using (q.graphPoint_smul (LipschitzWith.const (0:ℝ)) (0:ℝ)).symm
  add_mem' := by
    rintro P Q ⟨u,K,hu,rfl⟩ ⟨v,J,hv,rfl⟩
    exact ⟨_,_,hu.add hv,(q.graphPoint_add hu hv).symm⟩
  smul_mem' := by
    rintro c P ⟨u,K,hu,rfl⟩
    exact ⟨_,_,(lipschitzWith_smul c).comp hu,(q.graphPoint_smul hu c).symm⟩

noncomputable def closedGraph : Submodule ℝ q.GraphAmbient := q.lipschitzGraph.topologicalClosure

noncomputable abbrev Sobolev := q.closedGraph

lemma closedGraph_isClosed : IsClosed (q.closedGraph : Set q.GraphAmbient) :=
  q.lipschitzGraph.isClosed_topologicalClosure

instance : CompleteSpace q.Sobolev := q.closedGraph_isClosed.completeSpace_coe

noncomputable def valueProjection : q.GraphAmbient →L[ℝ] Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

noncomputable def gradientProjection : q.GraphAmbient →L[ℝ] Lp (Euc n) 2 q.atlasMeasure :=
  (ContinuousLinearMap.snd ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

@[simp] lemma valueProjection_graphPoint {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.valueProjection (q.graphPoint hu) = value hu := rfl
@[simp] lemma gradientProjection_graphPoint {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.gradientProjection (q.graphPoint hu) = q.gradient hu := rfl

lemma graph_norm_sq (P : q.GraphAmbient) :
    ‖P‖^2 = ‖q.valueProjection P‖^2+‖q.gradientProjection P‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 P

lemma graphPoint_mem {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.graphPoint hu ∈ q.closedGraph :=
  subset_closure (show q.graphPoint hu ∈ q.lipschitzGraph from ⟨u,K,hu,rfl⟩)

lemma exists_lipschitz_approximants (P : q.Sobolev) :
    ∃ (u : ℕ → X → ℝ) (K : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (K j) (u j)),
      Tendsto (fun j => q.graphPoint (hu j)) atTop (𝓝 (P : q.GraphAmbient)) := by
  have hp : (P : q.GraphAmbient) ∈ closure (q.lipschitzGraph : Set q.GraphAmbient) := P.property
  obtain ⟨p,hp,hlim⟩ := mem_closure_iff_seq_limit.mp hp
  choose u K hu he using hp
  refine ⟨u,K,hu,?_⟩
  have heq : p = fun j => q.graphPoint (hu j) := funext he
  rw [←heq]
  exact hlim

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGraph_zero_value (hz : IsCycle T) (P : q.Sobolev)
    (hP : q.valueProjection P = 0) : q.gradientProjection P = 0 := by
  obtain ⟨u,K,hu,hlim⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hlim
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hlim
  simp only [Function.comp_def,q.valueProjection_graphPoint,hP] at hv
  simp only [Function.comp_def,q.gradientProjection_graphPoint] at hg
  have hn := hv.norm
  simp only [norm_zero,norm_value] at hn
  exact q.gradient_closable hz u K hu hn _ hg

lemma closedGraph_value_injective (hz : IsCycle T) :
    Function.Injective (fun P : q.Sobolev => q.valueProjection P) := by
  intro P Q he
  change q.valueProjection P = q.valueProjection Q at he
  have hd : q.valueProjection (↑(P-Q) : q.GraphAmbient) = 0 := by
    change q.valueProjection ((P : q.GraphAmbient)-(Q : q.GraphAmbient)) = 0
    rw [map_sub,he,sub_self]
  have hg := q.closedGraph_zero_value hz (P-Q) hd
  have heq : (↑(P-Q) : q.GraphAmbient) = 0 := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact hd
    · exact hg
  exact sub_eq_zero.mp (Subtype.ext heq)

noncomputable def inclusion : q.Sobolev →L[ℝ] Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  q.valueProjection.comp q.closedGraph.subtypeL

noncomputable def closedGradient : q.Sobolev →L[ℝ] Lp (Euc (k+1)) 2 q.atlasMeasure :=
  q.gradientProjection.comp q.closedGraph.subtypeL

lemma inclusion_injective (hz : IsCycle T) : Function.Injective q.inclusion :=
  q.closedGraph_value_injective hz

lemma sobolev_norm_sq (P : q.Sobolev) :
    ‖P‖^2 = ‖q.inclusion P‖^2 + ‖q.closedGradient P‖^2 := q.graph_norm_sq P

lemma closedGradient_closed (u : Lp ℝ 2 (MassMeasure.currentMassMeasure hT))
    (G : Lp (Euc (k+1)) 2 q.atlasMeasure) (P : ℕ → q.Sobolev)
    (hu : Tendsto (fun j => q.inclusion (P j)) atTop (𝓝 u))
    (hG : Tendsto (fun j => q.closedGradient (P j)) atTop (𝓝 G)) :
    ∃ Q : q.Sobolev, q.inclusion Q = u ∧ q.closedGradient Q = G := by
  have hpair := hu.prodMk_nhds hG
  have hh := ((WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) (Lp (Euc (k+1)) 2 q.atlasMeasure)).symm.continuous.tendsto (u,G)).comp hpair
  have hh' : Tendsto (fun j => (P j : q.GraphAmbient)) atTop
      (𝓝 (WithLp.toLp 2 (u,G))) := hh
  have hm : WithLp.toLp 2 (u,G) ∈ q.closedGraph :=
    q.closedGraph_isClosed.mem_of_tendsto hh' (Eventually.of_forall fun j => (P j).property)
  exact ⟨⟨_,hm⟩,rfl,rfl⟩

end CAT0Fillings.ChartGeometry
end

end OAI
