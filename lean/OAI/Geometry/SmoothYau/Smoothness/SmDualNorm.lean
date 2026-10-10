import Mathlib
import OAI.Geometry.SmoothYau.Geometry.PrepDualNorm
import OAI.Geometry.SmoothYau.Smoothness.ContinuousCompactSmoothJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance jetDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance jetDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance jetFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance jetFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

abbrev MetricJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × (CoordinateForm E × (E →L[ℝ] ℝ))

def metricJetMap (g : SmoothMetric E E) (z : MetricJet E) : CoordinateForm E × E :=
  (metricProfileTraceForm (selfMetricFlat g z.1) z.2.1 ((selfMetricFlat g z.1).inverse z.2.2),
    (InnerProductSpace.toDual ℝ E).symm z.2.2)

lemma contDiff_selfMetricFlat_inverse (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
    (contDiff_selfMetricFlat g).contDiffAt

lemma continuous_metricJetMap (g : SmoothMetric E E) : Continuous (metricJetMap g) := by
  have hB : Continuous (fun z : MetricJet E => selfMetricFlat g z.1) :=
    (contDiff_selfMetricFlat g).continuous.comp continuous_fst
  have ha : Continuous (fun z : MetricJet E => (selfMetricFlat g z.1).inverse z.2.2) :=
    ((contDiff_selfMetricFlat_inverse g).continuous.comp continuous_fst).clm_apply continuous_snd.snd
  exact (continuous_metricProfileTraceForm_comp hB continuous_snd.fst ha).prodMk
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp continuous_snd.snd)

def metricJetStrict (g : SmoothMetric E E) (z : MetricJet E) : Prop :=
  (metricJetMap g z).2 ≠ 0 ∧ quadraticPlaneStrict (metricJetMap g z).1 (metricJetMap g z).2

def metricJetFull (g : SmoothMetric E E) (z : MetricJet E) : Prop :=
  (metricJetMap g z).2 ≠ 0 ∧ quadraticPlaneFull (metricJetMap g z).1 (metricJetMap g z).2

lemma isOpen_metricJetStrict (g : SmoothMetric E E) : IsOpen {z | metricJetStrict g z} := by
  have h : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneStrict p.1 p.2} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (continuous_snd.continuousAt.eventually_ne hp.1).and
      (quadraticPlaneStrict_eventually hp.1 hp.2)
  exact h.preimage (continuous_metricJetMap g)

lemma isOpen_metricJetFull (g : SmoothMetric E E) : IsOpen {z | metricJetFull g z} := by
  have h : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneFull p.1 p.2} :=
    (isOpen_ne_fun continuous_snd continuous_const).inter isOpen_quadraticPlaneFull
  exact h.preimage (continuous_metricJetMap g)

omit [FiniteDimensional ℝ E] in
theorem compact_metricJet_stability (_g : SmoothMetric E E) (P : MetricJet E → Prop)
    (hP : IsOpen {z | P z}) {K : Set E} (hK : IsCompact K) {J : Set ℝ} (hJ : IsCompact J)
    {H : E × ℝ → CoordinateForm E} (hH : Continuous H)
    {l : E → E →L[ℝ] ℝ} (hl : Continuous l)
    (hgood : ∀ x ∈ K, ∀ c ∈ J, P (x,H (x,c),l x)) :
    ∃ ε > 0, ∀ x ∈ K, ∀ c ∈ J, ∀ H' : CoordinateForm E, ∀ l' : E →L[ℝ] ℝ,
      ‖H'-H (x,c)‖ < ε → ‖l'-l x‖ < ε → P (x,H',l') := by
  let : PseudoEMetricSpace (MetricJet E) :=
    (inferInstance : PseudoMetricSpace (MetricJet E)).toPseudoEMetricSpace
  let f : E × ℝ → MetricJet E := fun z => (z.1,H z,l z.1)
  have hf : Continuous f := continuous_fst.prodMk (hH.prodMk (hl.comp continuous_fst))
  have hc := (hK.prod hJ).image hf
  have hsub : f '' (K ×ˢ J) ⊆ {z | P z} := by
    rintro z ⟨⟨x,c⟩,hx,rfl⟩
    exact hgood x hx.1 c hx.2
  obtain ⟨ε,hε,he⟩ := hc.exists_thickening_subset_open hP hsub
  refine ⟨ε,hε,?_⟩
  intro x hx c hc H' l' hH' hl'
  apply he
  apply mem_thickening_iff.mpr
  refine ⟨f (x,c),mem_image_of_mem f ⟨hx,hc⟩,?_⟩
  change dist (x,H',l') (x,H (x,c),l x) < ε
  rw [Prod.dist_eq,Prod.dist_eq,dist_self]
  exact max_lt hε (max_lt (by simpa only [dist_eq_norm] using hH')
    (by simpa only [dist_eq_norm] using hl'))

lemma metricJetStrict_actual (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    metricJetStrict g (x,actualCoordinateHessian g u x,fderiv ℝ u x) ↔
      coordinateMetricGradient g u x ≠ 0 ∧ actualProfileStrict g u x := by
  have hn : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 ↔
      coordinateMetricGradient g u x ≠ 0 := by
    constructor
    · intro hh h0
      have hd : fderiv ℝ u x = 0 := by
        simpa only [map_zero] using (selfMetricFlat_invertible g x).inverse_apply_eq.mp h0
      exact hh (by simp only [hd,map_zero])
    · exact coordinateMetricGradient_ne_zero_dual g u x
  exact and_congr_left (fun _ => hn)

lemma metricJetFull_actual (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    metricJetFull g (x,actualCoordinateHessian g u x,fderiv ℝ u x) ↔
      coordinateMetricGradient g u x ≠ 0 ∧ actualProfileFull g u x := by
  have hn : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 ↔
      coordinateMetricGradient g u x ≠ 0 := by
    constructor
    · intro hh h0
      have hd : fderiv ℝ u x = 0 := by
        simpa only [map_zero] using (selfMetricFlat_invertible g x).inverse_apply_eq.mp h0
      exact hh (by simp only [hd,map_zero])
    · exact coordinateMetricGradient_ne_zero_dual g u x
  exact and_congr_left (fun _ => hn)


end

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance smDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance smDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance smFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance smFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance smDerivNorm : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance smDerivSpace : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
local instance smJetNorm : NormedAddCommGroup (HessianJetData E) := inferInstance
local instance smJetSpace : NormedSpace ℝ (HessianJetData E) := inferInstance

def fullStrictJetMap (z : HessianJetData E) : CoordinateForm E × E :=
  (metricProfileTraceForm z.1.1 (metricHessianFromFullJet z) (z.1.1.inverse z.2.1),
    (InnerProductSpace.toDual ℝ E).symm z.2.1)
def fullStrictJetSet : Set (HessianJetData E) :=
  {z | (fullStrictJetMap z).2 ≠ 0 ∧
    quadraticPlaneStrict (fullStrictJetMap z).1 (fullStrictJetMap z).2}
lemma fullStrictJetMap_actual (g : SmoothMetric E E) (f : E → ℝ) (x : E) :
    metricScalarJet g f x ∈ fullStrictJetSet ↔
      coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x := by
  change metricJetStrict g (x,actualCoordinateHessian g f x,fderiv ℝ f x) ↔ _
  exact metricJetStrict_actual g f x
lemma continuousAt_fullStrictJetMap {z : HessianJetData E} (hz : z.1.1.IsInvertible) :
    ContinuousAt fullStrictJetMap z := by
  have hi : ContinuousAt (fun w : HessianJetData E => w.1.1.inverse) z :=
    (hz.contDiffAt_map_inverse (n:=∞)).continuousAt.comp
      (f:=fun w : HessianJetData E => w.1.1) (x:=z) continuous_fst.fst.continuousAt
  have ha : ContinuousAt (fun z : HessianJetData E => z.1.1.inverse z.2.1) z :=
    hi.clm_apply continuous_snd.fst.continuousAt
  have hh := continuousAt_metricHessianFromFullJet hz
  have ht : ContinuousAt (fun z : HessianJetData E =>
      metricProfileTraceForm z.1.1 (metricHessianFromFullJet z) (z.1.1.inverse z.2.1)) z := by
    have hB : ContinuousAt (fun w : HessianJetData E => w.1.1) z :=
      continuous_fst.fst.continuousAt
    unfold metricProfileTraceForm
    exact (((hh.clm_apply ha).clm_apply ha).smul hB).add
      ((continuousAt_const.add ((hB.clm_apply ha).clm_apply ha)).smul hh)
  exact ht.prodMk ((InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
    continuous_snd.fst.continuousAt)
lemma metricScalarJet_strict_interior (g : SmoothMetric E E) (f : E → ℝ) (x : E)
    (h : coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    metricScalarJet g f x ∈ interior (fullStrictJetSet (E:=E)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have ho : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneStrict p.1 p.2} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (continuous_snd.continuousAt.eventually_ne hp.1).and
      (quadraticPlaneStrict_eventually hp.1 hp.2)
  exact (continuousAt_fullStrictJetMap (selfMetricFlat_invertible g x))
    (ho.mem_nhds ((fullStrictJetMap_actual g f x).mpr h))

theorem compact_actual_strict_metric_stability (g₀ : SmoothMetric E E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hs : ∀ x ∈ K, coordinateMetricGradient g₀ f x ≠ 0 ∧ actualProfileStrict g₀ f x) :
    ∃ δ>0, ∀ g : SmoothMetric E E,
      (∀ x ∈ K, ‖selfMetricFlat g x-selfMetricFlat g₀ x‖<δ ∧
        ‖fderiv ℝ (selfMetricFlat g) x-fderiv ℝ (selfMetricFlat g₀) x‖<δ) →
      ∀ x ∈ K, coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x := by
  obtain ⟨δ,hδ,hstable⟩ := compact_map_uniform_interior hK
    (continuous_metricScalarJet g₀ hf)
    (fun x hx => metricScalarJet_strict_interior g₀ f x (hs x hx))
  refine ⟨δ,hδ,?_⟩
  intro g hg x hx
  exact (fullStrictJetMap_actual g f x).mp (hstable x hx (metricScalarJet g f x)
    (dist_metricScalarJet_lt g g₀ f x hδ (hg x hx).1 (hg x hx).2))

end YauCounterexamples
end

end OAI
