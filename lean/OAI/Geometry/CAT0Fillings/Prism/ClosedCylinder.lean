import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Charts.Postcompose
import OAI.Geometry.CAT0Fillings.Charts.CurrentAxioms
import OAI.Geometry.CAT0Fillings.Prism.Chart
import OAI.Geometry.CAT0Fillings.Prism.Mass

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal ENNReal Topology

abbrev ClosedCylinder (X : Type*) := Icc (0:ℝ) 1 × X
noncomputable def cylinderClamp {X : Type*} (p : ℝ × X) : ClosedCylinder X :=
  (projIcc 0 1 (by norm_num) p.1,p.2)
def cylinderEmbed {X : Type*} (p : ClosedCylinder X) : ℝ × X := (p.1.val,p.2)

lemma cylinderClamp_lipschitz {X : Type*} [MetricSpace X] :
    LipschitzWith 1 (cylinderClamp (X := X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq,cylinderClamp]
  refine max_le ?_ (le_max_right _ _)
  apply le_trans _ (le_max_left _ _)
  simpa only [NNReal.coe_one,one_mul] using
    (LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1)).dist_le_mul p.1 q.1

lemma cylinderEmbed_isometry {X : Type*} [MetricSpace X] :
    Isometry (cylinderEmbed (X := X)) := by
  exact (isometry_subtype_coe).prodMap isometry_id

lemma cylinderEmbed_clamp {X : Type*} (p : ℝ × X) (hp : p.1 ∈ Icc (0:ℝ) 1) :
    cylinderEmbed (cylinderClamp p) = p := by
  dsimp [cylinderEmbed,cylinderClamp]
  rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) hp]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma prism_clamp_bilipschitz : ∃ J : ℝ≥0,
    AntilipschitzWith J (cylinderClamp ∘ C.prism.param) := by
  obtain ⟨L,J,hL,hJ⟩ := C.prism.bilipschitz
  refine ⟨J,?_⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have hx : cylinderEmbed (cylinderClamp (C.prism.param x)) = C.prism.param x :=
    cylinderEmbed_clamp _ x.2.1
  have hy : cylinderEmbed (cylinderClamp (C.prism.param y)) = C.prism.param y :=
    cylinderEmbed_clamp _ y.2.1
  have hd := cylinderEmbed_isometry.dist_eq (cylinderClamp (C.prism.param x))
    (cylinderClamp (C.prism.param y))
  simpa only [Function.comp_apply,←hd,hx,hy] using hJ.le_mul_dist x y

noncomputable def closedPrism : IntegerChart (ClosedCylinder X) (k+1) :=
  C.prism.postcompose cylinderClamp_lipschitz C.prism_clamp_bilipschitz.choose_spec

lemma closedPrism_action : C.closedPrism.action = pushCurrent cylinderClamp C.prism.action :=
  C.prism.postcompose_action _ _

lemma closedPrism_image : C.closedPrism.image = cylinderClamp '' C.prism.image :=
  C.prism.postcompose_image _ _

lemma closedPrism_image_disjoint {D : IntegerChart X k} (hCD : Disjoint C.image D.image) :
    Disjoint C.closedPrism.image D.closedPrism.image := by
  rw [C.closedPrism_image,D.closedPrism_image]
  apply Set.disjoint_left.mpr
  rintro p ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hxI : x.1 ∈ Icc (0:ℝ) 1 := (C.prism_image ▸ hx).1
  have hyI : y.1 ∈ Icc (0:ℝ) 1 := (D.prism_image ▸ hy).1
  have hxy : y = x := by
    simpa only [cylinderEmbed_clamp _ hxI,cylinderEmbed_clamp _ hyI] using
      congrArg cylinderEmbed heq
  exact (Set.disjoint_left.mp (C.prism_image_disjoint hCD) hx) (hxy ▸ hy)

lemma mass_closedPrism_le [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [Nonempty X] : mass C.closedPrism.action ≤ (k+1:ℝ)*mass C.action := by
  obtain ⟨μ,hfin,hμ,heq⟩ := C.action_isMetricCurrent.exists_controls_mass_eq
  let : IsFiniteMeasure μ := hfin
  let ν : Measure (ℝ × X) := (k+1:ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod μ
  have hν : Controls C.prism.action ν := C.prism_controls hμ
  have hc := pushCurrent_controls C.prism.action_isMetricCurrent hν cylinderClamp_lipschitz
  simp only [one_pow,ENNReal.coe_one,one_smul] at hc
  rw [C.closedPrism_action]
  apply (mass_le_measure (inferInstance : IsFiniteMeasure (ν.map cylinderClamp)) hc).trans_eq
  rw [Measure.real,Measure.map_apply cylinderClamp_lipschitz.continuous.measurable
    MeasurableSet.univ,preimage_univ]
  change ν.real univ = _
  dsimp [ν]
  rw [heq,measureReal_nnreal_smul_apply]
  simp [measureReal_def,←Set.univ_prod_univ,Measure.prod_prod]

end IntegerChart

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

end CAT0Fillings
end
end

end OAI
