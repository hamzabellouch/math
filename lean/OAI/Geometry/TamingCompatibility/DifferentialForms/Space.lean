import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ContDiffLinearEmbedding

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
namespace TamingCompatibility.SmoothAlmostComplex

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

structure AlmostComplexStructure (X : Type*) [TopologicalSpace X]
    [ChartedSpace Space X] [IsManifold Model ∞ X] where
  endomorphism : (x : X) → TangentSpace Model x →L[ℝ] TangentSpace Model x
  square : ∀ x v, endomorphism x (endomorphism x v) = -v
  smooth : ContMDiff Model.tangent Model.tangent ∞
    (fun p : TangentBundle Model X =>
      (⟨p.proj, endomorphism p.proj p.2⟩ : TangentBundle Model X))

lemma contMDiffAt_localConstant
    (e : Trivialization Space (π Space (TangentSpace Model : X → Type)))
    [MemTrivializationAtlas e] {x : X} (hx : x ∈ e.baseSet) (v : Space) :
    ContMDiffAt Model Model.tangent ∞
      (fun y => (⟨y, e.symmL ℝ y v⟩ : TangentBundle Model X)) x := by
  apply (e.contMDiffAt_section_iff hx).mpr
  have hc : ContMDiffAt Model Model ∞ (fun _ : X => v) x := contMDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simp [e.symmL_apply hy, e.mk_symm hy, e.apply_symm_apply (show (y, v) ∈ e.target by simpa only [Trivialization.mem_target] using hy)]

lemma contMDiffOn_coord_apply (J : AlmostComplexStructure X)
    (e : Trivialization Space (π Space (TangentSpace Model : X → Type)))
    [MemTrivializationAtlas e] (v : Space) :
    ContMDiffOn Model Model ∞
      (fun y => e.continuousLinearMapAt ℝ y (J.endomorphism y (e.symmL ℝ y v)))
      e.baseSet := by
  intro y hy
  have hs := J.smooth.contMDiffAt.comp y (contMDiffAt_localConstant e hy v)
  have hc := (e.contMDiffAt_section_iff hy).mp hs
  apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hz _

def coord (J : AlmostComplexStructure X)
    (e : Trivialization Space (π Space (TangentSpace Model : X → Type)))
    [MemTrivializationAtlas e] (y : X) :
    Space →L[ℝ] Space :=
  (e.continuousLinearMapAt ℝ y).comp ((J.endomorphism y).comp (e.symmL ℝ y))

lemma contDiffOn_coord_chart (J : AlmostComplexStructure X) (x : X) :
    ContDiffOn ℝ ∞
      (fun z => coord J (trivializationAt Space (TangentSpace Model) x)
        ((extChartAt Model x).symm z))
      (extChartAt Model x).target := by
  rw [contDiffOn_clm_apply]
  intro v
  rw [← contMDiffOn_iff_contDiffOn]
  change ContMDiffOn Model Model ∞
    ((fun y => (trivializationAt Space (TangentSpace Model) x).continuousLinearMapAt ℝ y
      (J.endomorphism y ((trivializationAt Space (TangentSpace Model) x).symmL ℝ y v))) ∘
        (extChartAt Model x).symm) _
  apply (contMDiffOn_coord_apply J (trivializationAt Space (TangentSpace Model) x) v).comp
    (contMDiffOn_extChartAt_symm x)
  intro z hz
  simpa only [Set.mem_preimage, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
    (extChartAt Model x).map_target hz

end TamingCompatibility.SmoothAlmostComplex

namespace TamingCompatibility.ManifoldForms

open TamingCompatibility.FormSmoothness TamingCompatibility.SmoothAlmostComplex Bundle

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def jAction (J : SmoothAlmostComplex.AlmostComplexStructure X) (α : Form X k) : Form X k :=
  fun x => (α x).compContinuousLinearMap (J.endomorphism x)

lemma pullback_jAction_chart (J : SmoothAlmostComplex.AlmostComplexStructure X)
    (α : Form X k) (x : X) {z : Space} (hz : z ∈ (extChartAt Model x).target) :
    pullback (jAction J α) (extChartAt Model x).symm z =
      (pullback α (extChartAt Model x).symm z).compContinuousLinearMap
        (SmoothAlmostComplex.coord J (trivializationAt Space (TangentSpace Model) x)
          ((extChartAt Model x).symm z)) := by
  let e := extChartAt Model x
  let te := trivializationAt Space (TangentSpace Model) x
  have hs : e.symm z ∈ (chartAt Space x).source := by
    simpa only [e, extChartAt_source] using e.map_target hz
  have ht : e.symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet] using hs
  have hd : mfderiv Model Model e.symm z = te.symmL ℝ (e.symm z) := by
    rw [TangentBundle.symmL_trivializationAt hs]
    change mfderiv Model Model e.symm z =
      mfderivWithin Model Model e.symm (Set.range Model) (e (e.symm z))
    rw [e.right_inv hz]
    simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  apply ContinuousAlternatingMap.ext
  intro v
  change (α (e.symm z)) (fun i => J.endomorphism (e.symm z)
      (mfderiv Model Model e.symm z (v i))) =
    (α (e.symm z)) (fun i => mfderiv Model Model e.symm z
      (te.continuousLinearMapAt ℝ (e.symm z) (J.endomorphism (e.symm z)
        (te.symmL ℝ (e.symm z) (v i)))))
  apply congrArg (α (e.symm z))
  funext i
  rw [hd]
  exact (te.symmL_continuousLinearMapAt (R := ℝ) ht
    (J.endomorphism (e.symm z) (te.symmL ℝ (e.symm z) (v i)))).symm

theorem Smooth.jAction {α : Form X k} (hα : Smooth α)
    (J : SmoothAlmostComplex.AlmostComplexStructure X) : Smooth (jAction J α) := by
  apply smooth_of_charts
  intro x
  apply ((smooth_chart α hα x).compAlternating
    (SmoothAlmostComplex.contDiffOn_coord_chart J x)).congr
  intro z hz
  exact pullback_jAction_chart J α x hz

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma IsSmooth.jAction {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) : IsSmooth (jAction J α) := by
  exact ManifoldForms.Smooth.jAction hα
    (⟨J.endomorphism, J.square, J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X)

lemma IsSmooth.invariantPart {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) : IsSmooth (invariantPart J α) :=
  (hα.add (hα.jAction J)).smul _

lemma IsSmooth.antiInvariantPart {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) : IsSmooth (antiInvariantPart J α) := by
  change IsSmooth ((1 / 2 : ℝ) • (α + -TamingCompatibility.jAction J α))
  convert (hα.add ((hα.jAction J).smul (-1))).smul (1 / 2 : ℝ) using 1
  ext x v
  simp
end TamingCompatibility

end

end OAI
