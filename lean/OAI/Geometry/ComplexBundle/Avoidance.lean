import OAI.Geometry.ComplexBundle.Incidence
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace OAI

noncomputable section

/-! Avoidance of lower-dimensional incidence images in local manifold charts. -/

section
open scoped MeasureTheory ENNReal NNReal Topology
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.Incidence

/-- Local smoothness on an open coordinate domain suffices; convexity and
compactness of the whole coordinate domain are not assumptions. -/
theorem smoothOn_open_dimH_image_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) :
    dimH (f '' s) ≤ finrank ℝ E := by
  apply le_trans (dimH_image_le_of_locally_lipschitzOn ?_)
    ((dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E))
  intro x hx
  obtain ⟨C,t,ht,hL⟩ := ((hf x hx).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨C,t,nhdsWithin_le_nhds ht,hL⟩

/-- The lower-dimensional smooth image is null for top-dimensional Hausdorff
measure, which is an additive Haar measure on the target. -/
theorem smoothOn_open_image_null {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (hd : finrank ℝ E < finrank ℝ F) : μH[finrank ℝ F] (f '' s)=0 := by
  have h : dimH (f '' s) < (finrank ℝ F : ℝ≥0∞) :=
    (smoothOn_open_dimH_image_le hs hf).trans_lt (Nat.cast_lt.mpr hd)
  simpa only [NNReal.coe_natCast] using
    (hausdorffMeasure_of_dimH_lt (d := (finrank ℝ F : ℝ≥0)) h)

/-- A countable family of smaller-dimensional smooth coordinate images
cannot exhaust the parameter space. The null-image claims are proved here. -/
theorem exists_outside_countable_smooth_images {ι F : Type*} [Countable ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] (s : ∀ i, Set (E i)) (f : ∀ i, E i → F)
    (hs : ∀ i, IsOpen (s i)) (hf : ∀ i, ContDiffOn ℝ 1 (f i) (s i))
    (hd : ∀ i, finrank ℝ (E i)<finrank ℝ F) :
    ∃ v : F, ∀ i, v ∉ f i '' s i := by
  borelize F
  have hn : μH[finrank ℝ F] (⋃ i, f i '' s i)=0 :=
    measure_iUnion_null (fun i => smoothOn_open_image_null (hs i) (hf i) (hd i))
  have hne : (⋃ i, f i '' s i) ≠ univ := by
    intro h
    rw [h] at hn
    have hp : 0<μH[finrank ℝ F] (univ : Set F) :=
      isOpen_univ.measure_pos _ Set.univ_nonempty
    exact (ne_of_gt hp) hn
  by_contra h
  push Not at h
  apply hne
  apply Set.eq_univ_of_forall
  intro v
  obtain ⟨i,hi⟩ := h v
  exact Set.mem_iUnion.mpr ⟨i,hi⟩

end Kaplansky.Incidence

end

section
open Set
open scoped Topology Manifold ContDiff
namespace Kaplansky
variable {X B Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace B] [ChartedSpace X B] [IsManifold 𝓘(ℝ,X) ∞ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual chart domain restricted to a bundle trivializing open set. -/
def localChartDomain (U : B → Set B) (x : B) : Set X :=
  (chartAt X x).target ∩ (chartAt X x).symm ⁻¹' U x

omit [NormedSpace ℝ X] [IsManifold 𝓘(ℝ, X) ∞ B] in
theorem localChartDomain_open (U : B → Set B) (hU : ∀ x, IsOpen (U x)) (x : B) :
    IsOpen (localChartDomain (X := X) U x) :=
  (chartAt X x).continuousOn_symm.isOpen_inter_preimage (chartAt X x).open_target (hU x)

theorem localChartDomain_smooth (U : B → Set B) (f : B → Z) (x : B)
    (hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Z) ∞ f (U x)) :
    ContDiffOn ℝ ∞ (fun z => f ((chartAt X x).symm z)) (localChartDomain U x) := by
  apply ContMDiffOn.contDiffOn
  exact hf.comp ((contMDiffOn_chart_symm (I := 𝓘(ℝ,X)) (x := x)).mono inter_subset_left)
    (fun _ hz => hz.2)

omit [NormedSpace ℝ X] [IsManifold 𝓘(ℝ, X) ∞ B] in
/-- A countable choice of actual base charts covers the manifold while also
respecting the prescribed open neighborhoods. -/
theorem exists_countable_local_chart_cover [LindelofSpace B]
    (U : B → Set B) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x) :
    ∃ c : Set B, c.Countable ∧ ∀ y, ∃ x ∈ c,
      y ∈ U x ∧ y ∈ (chartAt X x).source ∧
      (chartAt X x) y ∈ localChartDomain U x ∧
      (chartAt X x).symm ((chartAt X x) y)=y := by
  let O x := U x ∩ (chartAt X x).source
  have ho : ∀ x, IsOpen (O x) := fun x => (hU x).inter (chartAt X x).open_source
  have hcov : (univ : Set B) ⊆ ⋃ x, O x := by
    intro y _
    exact mem_iUnion.mpr ⟨y,hxU y,mem_chart_source X y⟩
  obtain ⟨c,hc,hcov⟩ := isLindelof_univ.elim_countable_subcover O ho hcov
  refine ⟨c,hc,fun y => ?_⟩
  obtain ⟨x,hxc,hxy⟩ : ∃ x ∈ c, y ∈ O x := by
    simpa only [mem_iUnion,exists_prop] using hcov (mem_univ y)
  have he := (chartAt X x).left_inv hxy.2
  refine ⟨x,hxc,hxy.1,hxy.2,⟨(chartAt X x).mapsTo hxy.2,?_⟩,he⟩
  simpa only [mem_preimage,he] using hxy.1

end Kaplansky

end

section
open scoped ContDiff Topology MeasureTheory
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.SmoothKernel.SurjectiveFamily
variable {X V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
local instance : CompleteSpace W := FiniteDimensional.complete ℂ W
variable (A : SurjectiveFamily X V W)

theorem fromModel_contDiffAt (hA : ContDiff ℝ ∞ A.map) (i x : X) (hx : x ∈ A.baseSet i) :
    ContDiffAt ℝ ∞ (A.fromModel i) x := by
  have hc : ContDiff ℂ ∞ (fun P : V →L[ℂ] V =>
      P.comp (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
        (A.modelEquiv i).toContinuousLinearMap)) := contDiff_id.clm_comp contDiff_const
  exact (hc.restrict_scalars ℝ).contDiffAt.comp x
    (((kernelProjection_smooth (A.rightInverse i) (A.map x) hx).restrict_scalars ℝ).comp x hA.contDiffAt)

def kernelParameterization (i : X) (p : X × KernelModel V W) : V := A.fromModel i p.1 p.2

theorem kernelParameterization_smooth (hA : ContDiff ℝ ∞ A.map) (i : X) :
    ContDiffOn ℝ ∞ (A.kernelParameterization i) (A.baseSet i ×ˢ univ) := by
  intro p hp
  have hc := (ContinuousLinearMap.restrictScalarsL ℂ (KernelModel V W) V ℝ ℝ).contDiff.contDiffAt.comp p.1
    (A.fromModel_contDiffAt hA i p.1 hp.1)
  exact ((hc.comp p contDiffAt_fst).clm_apply contDiffAt_snd).contDiffWithinAt

variable [FiniteDimensional ℝ X]

omit [FiniteDimensional ℂ V] in
theorem exists_countable_baseSet_cover :
    ∃ c : Set X, c.Countable ∧ ∀ x : X, ∃ i ∈ c, x ∈ A.baseSet i := by
  have hc : (univ : Set X) ⊆ ⋃ i, A.baseSet i := by
    intro x _
    exact mem_iUnion.mpr ⟨x,A.center_mem x⟩
  obtain ⟨c,hc,hcov⟩ := isLindelof_univ.elim_countable_subcover A.baseSet A.baseSet_open hc
  exact ⟨c,hc,fun x => by simpa only [Set.mem_iUnion,exists_prop] using hcov (mem_univ x)⟩

/-- The image of the ACTUAL kernel incidence subset is null. The proof uses a
countable cover of the constructed kernel charts, not a null-image premise. -/
theorem kernel_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (hA : ContDiff ℝ ∞ A.map)
    (hd : finrank ℝ (X × KernelModel V W)<finrank ℝ V) :
    μH[finrank ℝ V] {v : V | ∃ x, A.map x v=0}=0 := by
  obtain ⟨c,hc,hcov⟩ := A.exists_countable_baseSet_cover
  let := hc.toEncodable
  have hi (i : c) : μH[finrank ℝ V]
      (A.kernelParameterization i.val '' (A.baseSet i.val ×ˢ univ))=0 :=
    Kaplansky.Incidence.smoothOn_open_image_null ((A.baseSet_open i.val).prod isOpen_univ)
      ((A.kernelParameterization_smooth hA i.val).of_le (by simp)) hd
  apply measure_mono_null (t := ⋃ i : c, A.kernelParameterization i.val '' (A.baseSet i.val ×ˢ univ))
    ?_ (measure_iUnion_null hi)
  rintro v ⟨x,hx⟩
  obtain ⟨i,hi,hxi⟩ := hcov x
  apply mem_iUnion.mpr
  refine ⟨⟨i,hi⟩,(x,A.toModel i v),⟨hxi,mem_univ _⟩,?_⟩
  exact A.fromModel_toModel i x hxi v hx

/-- A parameter outside every actual kernel exists under the dimension gap. -/
theorem exists_avoiding_kernels (hA : ContDiff ℝ ∞ A.map)
    (hd : finrank ℝ (X × KernelModel V W)<finrank ℝ V) :
    ∃ v : V, ∀ x, A.map x v ≠ 0 := by
  borelize V
  have hn := A.kernel_incidence_image_null hA hd
  by_contra h
  push Not at h
  have he : {v : V | ∃ x, A.map x v=0}=univ := Set.eq_univ_of_forall h
  rw [he] at hn
  have hp : 0<μH[finrank ℝ V] (univ : Set V) := isOpen_univ.measure_pos _ Set.univ_nonempty
  exact (ne_of_gt hp) hn

end Kaplansky.SmoothKernel.SurjectiveFamily

end

section
open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q h : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l)

omit [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] in
theorem evaluation_target_rank_le (hs : ∀ y, Function.Surjective (ev y)) :
    q*s*l ≤ finrank ℂ V := by
  let A := graphEvaluation ev (0,(0,0))
  have ha : Function.Surjective A :=
    (tupleGraphRestriction_surjective 0 0).comp (hs 0)
  have hr := A.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr ha,finrank_top,tupleTarget_finrank] at hr
  omega

theorem graph_incidence_dimension_gap (hs : ∀ y, Function.Surjective (ev y))
    (hY : finrank ℝ Y=2*h) (hgap : h+s*k+t*l<q*s*l) :
    finrank ℝ ((Y × (GraphSlope s k × GraphSlope t l)) × KernelModel V (TupleTarget q s l))<
      finrank ℝ V := by
  rw [incidence_model_finrank,hY,finrank_real_of_complex]
  have hm := evaluation_target_rank_le ev hs
  simp only [Nat.mul_assoc] at *
  omega

/-- On one pair of Grassmann graph charts, the actual bad-parameter locus is
null under exactly the incidence dimension gap. -/
theorem graph_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (he : ContDiff ℝ ∞ ev) (hs : ∀ y, Function.Surjective (ev y))
    (hY : finrank ℝ Y=2*h) (hgap : h+s*k+t*l<q*s*l) :
    μH[finrank ℝ V] {v : V | ∃ (y : Y) (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph,
      ev y v i x ∈ b.toLinearMap.graph}=0 := by
  have hn := (graphFamily ev he hs).kernel_incidence_image_null
    (graphEvaluation_smooth ev he) (graph_incidence_dimension_gap ev hs hY hgap)
  have heq : {v : V | ∃ p, (graphFamily ev he hs).map p v=0}=
      {v : V | ∃ (y : Y) (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph} := by
    ext v
    simp only [Set.mem_ofPred_eq,graphFamily,graphEvaluation_zero_iff,Prod.exists]
  rw [heq] at hn
  exact hn

/-- A tuple is constructed outside all incidence kernels in these charts;
it is not supplied as a premise. Full Grassmann coverage is a separate step. -/
theorem exists_avoiding_graph_incidence (he : ContDiff ℝ ∞ ev)
    (hs : ∀ y, Function.Surjective (ev y)) (hY : finrank ℝ Y=2*h)
    (hgap : h+s*k+t*l<q*s*l) :
    ∃ v : V, ∀ y (a : GraphSlope s k) (b : GraphSlope t l),
      ¬ ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph := by
  obtain ⟨v,hv⟩ := (graphFamily ev he hs).exists_avoiding_kernels
    (graphEvaluation_smooth ev he) (graph_incidence_dimension_gap ev hs hY hgap)
  refine ⟨v,fun y a b hh => ?_⟩
  exact hv (y,(a,b)) ((graphEvaluation_zero_iff ev (y,(a,b)) v).mpr hh)

end Kaplansky.Incidence

end

open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {s k t l q : ℕ}

abbrev TupleOperators (q s k t l : ℕ) := Fin q → Components s k →L[ℂ] Components t l

def frameEvaluationLinear (F : GraphFrame s k) (G : GraphFrame t l) :
    TupleOperators q s k t l →ₗ[ℂ] TupleAmbient q s k t l where
  toFun T i := G.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((T i).comp F.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' T U := by
    funext i
    apply ContinuousLinearMap.ext
    intro x
    change G (T i (F.symm x)+U i (F.symm x))=G (T i (F.symm x))+G (U i (F.symm x))
    exact G.map_add _ _
  map_smul' c T := by
    funext i
    apply ContinuousLinearMap.ext
    intro x
    change G (c • T i (F.symm x))=c • G (T i (F.symm x))
    exact G.map_smul c _

def frameEvaluation (F : GraphFrame s k) (G : GraphFrame t l) :
    TupleOperators q s k t l →L[ℂ] TupleAmbient q s k t l :=
  (frameEvaluationLinear F G).toContinuousLinearMap

@[simp] theorem frameEvaluation_apply (F : GraphFrame s k) (G : GraphFrame t l)
    (T : TupleOperators q s k t l) (i : Fin q) (x : GraphAmbient s k) :
    frameEvaluation F G T i x=G (T i (F.symm x)) := rfl

theorem frameEvaluation_surjective (F : GraphFrame s k) (G : GraphFrame t l) :
    Function.Surjective (frameEvaluation (q := q) F G) := by
  intro C
  refine ⟨fun i => G.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((C i).comp F.toContinuousLinearEquiv.toContinuousLinearMap),?_⟩
  funext i
  apply ContinuousLinearMap.ext
  intro x
  change G (G.symm (C i (F (F.symm x))))=C i x
  simp

theorem frame_incidence_iff (F : GraphFrame s k) (G : GraphFrame t l)
    (T : TupleOperators q s k t l) (a : GraphSlope s k) (b : GraphSlope t l) :
    (∀ i, ∀ x ∈ graphPlane F a.toLinearMap, T i x ∈ graphPlane G b.toLinearMap) ↔
      ∀ i, ∀ x ∈ a.toLinearMap.graph, frameEvaluation F G T i x ∈ b.toLinearMap.graph := by
  constructor
  · intro h i x hx
    have hi : F.symm x ∈ graphPlane F a.toLinearMap := by simpa using hx
    exact h i (F.symm x) hi
  · intro h i x hx
    have hi : F x ∈ a.toLinearMap.graph := hx
    have hh := h i (F x) hi
    change G (T i x) ∈ b.toLinearMap.graph
    simpa only [frameEvaluation_apply,LinearEquiv.symm_apply_apply] using hh

def ChartBad (F : GraphFrame s k) (G : GraphFrame t l) : Set (TupleOperators q s k t l) :=
  {T | ∃ (a : GraphSlope s k) (b : GraphSlope t l),
    ∀ i, ∀ x ∈ graphPlane F a.toLinearMap, T i x ∈ graphPlane G b.toLinearMap}

/-- The actual bad tuples in any pair of graph charts form a null set over a
point; no restriction is placed on the positions of the two charts. -/
theorem chartBad_null (F : GraphFrame s k) (G : GraphFrame t l)
    [MeasurableSpace (TupleOperators q s k t l)] [BorelSpace (TupleOperators q s k t l)]
    (hgap : s*k+t*l<q*s*l) : μH[finrank ℝ (TupleOperators q s k t l)] (ChartBad (q := q) F G)=0 := by
  let ev : (Fin 0 → ℝ) → TupleOperators q s k t l →L[ℂ] TupleAmbient q s k t l :=
    fun _ => frameEvaluation F G
  have hn := graph_incidence_image_null (h := 0) ev contDiff_const
    (fun _ => frameEvaluation_surjective F G) (by simp) (by simpa using hgap)
  have he : {T : TupleOperators q s k t l | ∃ (y : Fin 0 → ℝ)
      (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph,
      ev y T i x ∈ b.toLinearMap.graph}=ChartBad F G := by
    ext T
    constructor
    · rintro ⟨_,a,b,hab⟩
      exact ⟨a,b,(frame_incidence_iff F G T a b).mpr hab⟩
    · rintro ⟨a,b,hab⟩
      exact ⟨0,a,b,(frame_incidence_iff F G T a b).mp hab⟩
  rw [he] at hn
  exact hn

end Kaplansky.Incidence

end

end OAI
