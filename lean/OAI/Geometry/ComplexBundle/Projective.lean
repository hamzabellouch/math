import OAI.Geometry.ComplexBundle.GrassmannManifold
import OAI.Geometry.ComplexBundle.Projection
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

namespace OAI

noncomputable section

/-! Projection models of complex projective space and products. -/

section
open Matrix Topology NormedSpace
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def projectionToGrassmann (p : projectionSpace (1+k) 1) : Grassmann 1 k :=
  ⟨(projectionLine p).map (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearMap,
    by rw [LinearEquiv.finrank_map_eq]; exact projectionLine_finrank p⟩

def columnFrame (i : Fin (1+k)) (p : projectionSpace (1+k) 1) : PlaneFrameMap 1 k :=
  (ContinuousLinearMap.proj (0 : Fin 1)).smulRight
    ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (unitProjectionColumn p i))

theorem columnFrame_injective (i : Fin (1+k)) (p : projectionSpace (1+k) 1)
    (hp : p ∈ projectionChartSet i) : Function.Injective (columnFrame i p) := by
  have hv : (EuclideanSpace.equiv (Fin (1+k)) ℂ) (unitProjectionColumn p i) ≠ 0 := by
    intro h
    have hz := (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective (h.trans (map_zero _).symm)
    have hn := unitProjectionColumn_norm p i hp
    rw [hz,norm_zero] at hn
    norm_num at hn
  intro u v huv
  have hs : (u 0-v 0) • ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (unitProjectionColumn p i))=0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr huv
  have h0 := sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hv)
  ext j
  have hj : j=0 := Fin.eq_zero j
  simpa only [hj] using h0

theorem columnFrame_point (i : Fin (1+k)) (p : projectionSpace (1+k) 1)
    (hp : p ∈ projectionChartSet i) :
    framePoint ⟨columnFrame i p,columnFrame_injective i p hp⟩ = projectionToGrassmann p := by
  apply Subtype.ext
  change LinearMap.range (columnFrame i p).toLinearMap =
    (projectionLine p).map (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearMap
  rw [projectionLine_eq_span p i hp,Submodule.map_span,Set.image_singleton]
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact (Submodule.span ℂ {_}).smul_mem (v 0) (Submodule.subset_span (Set.mem_singleton _))
  · intro hz
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨fun _ => c,rfl⟩

theorem continuousOn_columnFrame (i : Fin (1+k)) :
    ContinuousOn (columnFrame i) (projectionChartSet i) := by
  apply continuousOn_clm_apply.mpr
  intro v
  exact continuousOn_const.smul
    ((EuclideanSpace.equiv (Fin (1+k)) ℂ).continuous.comp_continuousOn
      (continuousOn_unitProjectionColumn i))

theorem continuous_projectionToGrassmann : Continuous (projectionToGrassmann (k := k)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨i,hi⟩ := exists_projectionColumn_ne_zero p
  have hc : ContinuousOn (projectionToGrassmann (k := k)) (projectionChartSet i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hf : Continuous (fun q : projectionChartSet (d := 1+k) i =>
        (⟨columnFrame i q.val,columnFrame_injective i q.val q.property⟩ : IndependentFrame 1 k)) :=
      (continuousOn_iff_continuous_domRestrict.mp (continuousOn_columnFrame i)).subtype_mk _
    exact (framePoint_continuous.comp hf).congr (fun q => columnFrame_point i q.val q.property)
  exact (hc p hi).continuousAt ((isOpen_projectionChartSet i).mem_nhds hi)

theorem projectionToGrassmann_injective : Function.Injective (projectionToGrassmann (k := k)) := by
  intro p q h
  apply projectionLine_injective
  exact (Submodule.map_injective_of_injective
    (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective) (congrArg Subtype.val h)

end Kaplansky.ComplexGrassmann

end

section
open Matrix Topology NormedSpace
open scoped ComplexOrder Matrix.Norms.L2Operator
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

/-- A nonvanishing representative of a line in a graph chart. -/
def graphLineVector (F : GraphFrame 1 k) (A : GraphSlope 1 k) : EuclideanSpace ℂ (Fin (1+k)) :=
  (EuclideanSpace.equiv (Fin (1+k)) ℂ).symm (F.symm ((fun _ => 1),A (fun _ => 1)))

@[simp] theorem graphLineVector_coordinates (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    (EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A) = F.symm ((fun _ => 1),A (fun _ => 1)) :=
  (EuclideanSpace.equiv (Fin (1+k)) ℂ).apply_symm_apply _

theorem graphLineVector_ne_zero (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphLineVector F A ≠ 0 := by
  intro h
  have hh := congrArg (fun v : EuclideanSpace ℂ (Fin (1+k)) =>
    (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) v)).1 (0 : Fin 1)) h
  rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply,map_zero,map_zero] at hh
  norm_num at hh

theorem continuous_graphLineVector (F : GraphFrame 1 k) : Continuous (graphLineVector F) := by
  apply (EuclideanSpace.equiv (Fin (1+k)) ℂ).symm.continuous.comp
  apply F.symm.toContinuousLinearEquiv.continuous.comp
  exact continuous_const.prodMk (continuous_id.clm_apply continuous_const)

def graphLineProjection (F : GraphFrame 1 k) (A : GraphSlope 1 k) : projectionSpace (1+k) 1 :=
  nonzeroVectorProjection (graphLineVector F A) (graphLineVector_ne_zero F A)

theorem continuous_graphLineProjection (F : GraphFrame 1 k) : Continuous (graphLineProjection F) := by
  apply Continuous.subtype_mk
  apply continuous_vectorOuter.comp
  exact ((continuous_graphLineVector F).norm.inv₀ (fun A =>
    norm_ne_zero_iff.mpr (graphLineVector_ne_zero F A))).smul (continuous_graphLineVector F)

theorem graphLineProjection_point (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    projectionToGrassmann (graphLineProjection F A) = slopePoint F A := by
  apply Subtype.ext
  change (projectionLine (nonzeroVectorProjection (graphLineVector F A) _)).map
    (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearMap = graphPlane F A.toLinearMap
  rw [nonzeroVectorProjection_line,Submodule.map_span,Set.image_singleton]
  symm
  apply eq_span_singleton_of_mem_of_finrank_eq_one (graphPlane_finrank F A.toLinearMap)
  · change (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A))).2 =
      A (F ((EuclideanSpace.equiv (Fin (1+k)) ℂ) (graphLineVector F A))).1
    rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply]
  · intro h
    apply graphLineVector_ne_zero F A
    exact (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective (h.trans (map_zero _).symm)

theorem projectionToGrassmann_surjective : Function.Surjective (projectionToGrassmann (k := k)) := by
  intro P
  obtain ⟨F,hF⟩ := grassmann_atlas_covers P
  refine ⟨graphLineProjection F (slopeCoordinate F P),?_⟩
  rw [graphLineProjection_point,slopePoint_coordinate F P hF]

/-- Projection and graph-atlas models of complex projective space agree
as sets of actual complex lines. -/
def projectiveProjectionEquiv (k : ℕ) : projectionSpace (1+k) 1 ≃ Grassmann 1 k :=
  Equiv.ofBijective projectionToGrassmann ⟨projectionToGrassmann_injective,projectionToGrassmann_surjective⟩

end Kaplansky.ComplexGrassmann

end

section
open Topology Set
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

theorem projectiveProjectionEquiv_symm_slopePoint (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    (projectiveProjectionEquiv k).symm (slopePoint F A) = graphLineProjection F A := by
  apply (projectiveProjectionEquiv k).injective
  rw [Equiv.apply_symm_apply]
  exact (graphLineProjection_point F A).symm

theorem continuous_projectiveProjectionEquiv_symm : Continuous (projectiveProjectionEquiv k).symm := by
  apply continuous_def.mpr
  intro U hU
  change ∀ F : GraphFrame 1 k, IsOpen (slopePoint F ⁻¹' ((projectiveProjectionEquiv k).symm ⁻¹' U))
  intro F
  have he : (fun A => (projectiveProjectionEquiv k).symm (slopePoint F A)) = graphLineProjection F :=
    funext (projectiveProjectionEquiv_symm_slopePoint F)
  have hc : Continuous (fun A => (projectiveProjectionEquiv k).symm (slopePoint F A)) :=
    he ▸ continuous_graphLineProjection F
  exact hc.isOpen_preimage U hU

/-- Identification of the compact orthogonal-projection model with the
ordinary smooth graph-chart model of complex projective space. -/
def projectiveProjectionHomeomorph (k : ℕ) : projectionSpace (1+k) 1 ≃ₜ Grassmann 1 k where
  toEquiv := projectiveProjectionEquiv k
  continuous_toFun := continuous_projectionToGrassmann
  continuous_invFun := continuous_projectiveProjectionEquiv_symm

instance projectiveGrassmannT2 : T2Space (Grassmann 1 k) :=
  (projectiveProjectionHomeomorph k).t2Space

instance projectiveGrassmannCompact : CompactSpace (Grassmann 1 k) :=
  (projectiveProjectionHomeomorph k).compactSpace

end Kaplansky.ComplexGrassmann

open Topology Set
open scoped Manifold ContDiff BigOperators
namespace Kaplansky.ComplexGrassmann
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

abbrev ProjectiveProduct := ∀ i, Grassmann 1 (K i)
abbrev ProjectiveProductModel := ∀ i, GraphSlope 1 (K i)

instance projectiveProductChartedSpace :
    ChartedSpace (ProjectiveProductModel K) (ProjectiveProduct K) :=
  inferInstanceAs (ChartedSpace (ModelPi (fun i => GraphSlope 1 (K i))) (ProjectiveProduct K))

instance projectiveProductRealManifold :
    IsManifold 𝓘(ℝ,ProjectiveProductModel K) ∞ (ProjectiveProduct K) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e,he,rfl⟩ ⟨f,hf,rfl⟩
  have he' : ∀ i, ∃ F : GraphFrame 1 (K i), grassmannChart F = e i := fun i => he i (mem_univ i)
  have hf' : ∀ i, ∃ F : GraphFrame 1 (K i), grassmannChart F = f i := fun i => hf i (mem_univ i)
  choose F hF using he'
  choose G hG using hf'
  have hfe : e = fun i => grassmannChart (F i) := funext (fun i => (hF i).symm)
  have hge : f = fun i => grassmannChart (G i) := funext (fun i => (hG i).symm)
  subst e; subst f
  simp only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.comp_def,id_eq,
    Set.range_id,Set.inter_univ,Set.preimage_id]
  apply contDiffOn_pi.mpr
  intro i
  have h := (grassmann_chart_transition_smooth (F i) (G i)).restrict_scalars ℝ
  apply h.comp ((ContinuousLinearMap.proj i : ProjectiveProductModel K →L[ℝ] GraphSlope 1 (K i)).contDiff.contDiffOn)
  intro A hA
  change A ∈ (OpenPartialHomeomorph.pi (fun i => grassmannChart (F i))).target ∧
    (OpenPartialHomeomorph.pi (fun i => grassmannChart (F i))).symm A ∈
      (OpenPartialHomeomorph.pi (fun i => grassmannChart (G i))).source at hA
  exact (inGraphChart_iff_unit (F i) (G i) (A i)).mp (hA.2 i (mem_univ i))

instance projectiveProductCompact : CompactSpace (ProjectiveProduct K) := inferInstance
instance projectiveProductT2 : T2Space (ProjectiveProduct K) := inferInstance

theorem projectiveProduct_real_finrank :
    Module.finrank ℝ (ProjectiveProductModel K) = 2*∑ i, K i := by
  rw [Module.finrank_pi_fintype]
  simp only [graph_slope_real_finrank,mul_one]
  exact (Finset.mul_sum ..).symm

end Kaplansky.ComplexGrassmann

end

open Topology Set
open scoped Manifold ContDiff
namespace Kaplansky.ComplexGrassmann
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

/-- Coordinate projections of the actual finite projective product are smooth. -/
theorem contMDiff_projectiveProduct_apply (i : ι) :
    ContMDiff 𝓘(ℝ,ProjectiveProductModel K) 𝓘(ℝ,GraphSlope 1 (K i)) ∞
      (fun P : ProjectiveProduct K => P i) := by
  intro P
  choose F hF using fun j => grassmann_atlas_covers (P j)
  let e := OpenPartialHomeomorph.pi (fun j => grassmannChart (F j))
  have he : e ∈ atlas (ProjectiveProductModel K) (ProjectiveProduct K) :=
    ⟨_,(fun j _ => Set.mem_range_self (F j)),rfl⟩
  have hP : P ∈ e.source := fun j _ => hF j
  have hchart : ContMDiffAt 𝓘(ℝ,ProjectiveProductModel K) 𝓘(ℝ,ProjectiveProductModel K) ∞ e P :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hP
  have hc := (ContinuousLinearMap.proj i : ProjectiveProductModel K →L[ℝ] GraphSlope 1 (K i)).contDiff.contDiffAt.contMDiffAt.comp P hchart
  have hi : grassmannChart (F i) ∈ IsManifold.maximalAtlas 𝓘(ℝ,GraphSlope 1 (K i)) ∞ (Grassmann 1 (K i)) :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self (F i))
  have hs := contMDiffAt_symm_of_mem_maximalAtlas hi
    (show e P i ∈ (grassmannChart (F i)).target by simp)
  apply (hs.comp P hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hP] with Q hQ
  exact ((grassmannChart (F i)).left_inv (hQ i (mem_univ i))).symm

end Kaplansky.ComplexGrassmann

end

end OAI
