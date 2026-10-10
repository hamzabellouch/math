import OAI.Combinatorics.SparsestCut.ContractionAverage

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.VertexMeasure
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => (CubePoincare.cube (m:=m))
local instance {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSpace (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
local instance {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
lemma cube_measurable (R : ℝ) : MeasurableSet (RoundedCharts.cube (m:=m) R) := by
  rw [show RoundedCharts.cube (m:=m) R=(⋂ j : Fin m, {x : E | |x j|<R}) by ext x; simp [RoundedCharts.cube]]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_lt (by fun_prop) measurable_const
lemma regular_measurable (u : Fin N → E) (τ : ℝ) : MeasurableSet {x | RoundedCharts.regular u τ x} := by
  rw [show {x | RoundedCharts.regular u τ x}=(⋂ i : Fin N, ⋂ k : ℤ, {x : E | inner ℝ (u i) x ≠ (k:ℝ)*τ}) by ext x; simp [RoundedCharts.regular]]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro k
  exact (isClosed_eq (by fun_prop : Continuous (fun x : E => inner ℝ (u i) x)) continuous_const).measurableSet.compl
lemma integer_measurable (u : Fin N → E) (τ : ℝ) : Measurable (RoundedCharts.integerLabel u τ) := by
  apply Measurable.of_eval
  intro i
  exact Int.measurable_floor.comp (by fun_prop)
open Classical in
def label (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) (x : E) : RoundedCharts.Vertex u τ :=
  if h : x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x then
    ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,h.1,h.2,rfl⟩ else v₀
lemma label_measurable (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) :
    Measurable (label u τ s v₀) := by
  classical
  have hh : Measurable (fun x : E => if x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x then
      (s,RoundedCharts.integerLabel (u s) τ x) else v₀.val) :=
    (measurable_const.prodMk (integer_measurable (u s) τ)).ite ((cube_measurable 2).inter (regular_measurable (u s) τ)) measurable_const
  have hval : Measurable (fun x => (label u τ s v₀ x).val) := by
    convert hh using 1
    funext x
    by_cases hgood : x ∈ RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x <;>
      simp [label, hgood]
  exact hval.subtype_mk
lemma ae_good (u : Fin N → E) (hu : ∀ i, u i≠0) (τ : ℝ) :
    ∀ᵐ x : E ∂μ, x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular u τ x := by
  filter_upwards [CubeGeometry.cube_mem (m:=m), CubeGeometry.cube_ac.ae_le (RoundedCharts.ae_regular u τ hu)] with x hx hr
  exact ⟨fun j => (hx j).trans (by norm_num),hr⟩
lemma vertex_nonempty (u : Fin S → Fin N → E) (hu : ∀ s i, u s i≠0) (τ : ℝ) (s : Fin S) :
    Nonempty (RoundedCharts.Vertex u τ) := by
  obtain ⟨x,hx,hr⟩ := (ae_good (u s) (hu s) τ).exists
  exact ⟨⟨(s,RoundedCharts.integerLabel (u s) τ x),x,hx,hr,rfl⟩⟩
def measure (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) : Measure (RoundedCharts.Vertex u τ) :=
  (μ).map (label u τ s v₀)
instance probability (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) :
    IsProbabilityMeasure (measure u τ s v₀) := by
  change IsProbabilityMeasure ((μ).map (label u τ s v₀))
  infer_instance
lemma finite_weights {V : Type u1} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : Measure V) [IsProbabilityMeasure ν] : (∑ v, ν.real {v})=1 := by
  have h : (∫ _ : V, (1:ℝ) ∂ν)=∑ v, ν.real {v} • (1:ℝ) := integral_fintype (integrable_const _)
  simp
lemma pair_average (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ)
    [Fintype (RoundedCharts.Vertex u τ)] (d : RoundedCharts.Vertex u τ → RoundedCharts.Vertex u τ → ℝ) :
    (∑ v, ∑ w, (measure u τ s v₀).real {v}*(measure u τ s v₀).real {w}*d v w)=
      ∫ z : E × E, d (label u τ s v₀ z.1) (label u τ s v₀ z.2) ∂(μ).prod μ := by
  let ν := measure u τ s v₀
  calc
    _ = ∫ z : RoundedCharts.Vertex u τ × RoundedCharts.Vertex u τ, d z.1 z.2 ∂ν.prod ν := by
      rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [show ({(v,w)} : Set (RoundedCharts.Vertex u τ × RoundedCharts.Vertex u τ))={v}×ˢ{w} by ext z; simp]
      rw [measureReal_prod_prod]
      rfl
    _ = _ := by
      change (∫ z, d z.1 z.2 ∂((μ).map (label u τ s v₀)).prod ((μ).map (label u τ s v₀)))=_
      rw [Measure.map_prod_map μ μ (label_measurable u τ s v₀) (label_measurable u τ s v₀)]
      exact integral_map ((label_measurable u τ s v₀).prodMap (label_measurable u τ s v₀)).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable
end
end UniformSparsestCut.VertexMeasure

end

end OAI
