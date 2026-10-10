import OAI.Geometry.ComplexBundle.Grassmann
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

noncomputable section

/-! Grassmannian frames, smooth manifold structure, and countability. -/

section
open scoped ContDiff
open Filter Topology
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

abbrev PlaneFrameMap (s k : ℕ) := (GraphHorizontal s) →L[ℂ] (Components s k)
abbrev IndependentFrame (s k : ℕ) := {B : (PlaneFrameMap s k) // Function.Injective B}

def framePoint (B : (IndependentFrame s k)) : (Grassmann s k) :=
  ⟨LinearMap.range B.val.toLinearMap,by
    rw [LinearMap.finrank_range_of_inj B.property]
    simp⟩

def frameTop (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) :=
  (ContinuousLinearMap.fst ℂ (GraphHorizontal s) (GraphVertical k)).comp
    (F.toContinuousLinearEquiv.toContinuousLinearMap.comp B)

def frameBottom (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) : (GraphSlope s k) :=
  (ContinuousLinearMap.snd ℂ (GraphHorizontal s) (GraphVertical k)).comp
    (F.toContinuousLinearEquiv.toContinuousLinearMap.comp B)

def frameSlope (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) : (GraphSlope s k) :=
  (frameBottom F B).comp (Ring.inverse (frameTop F B))

@[simp] theorem frameTop_apply (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (v : (GraphHorizontal s)) :
    frameTop F B v=(F (B v)).1 := rfl

@[simp] theorem frameBottom_apply (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (v : (GraphHorizontal s)) :
    frameBottom F B v=(F (B v)).2 := rfl

theorem frameTop_contDiff (F : (GraphFrame s k)) : ContDiff ℂ ∞ (frameTop F) :=
  contDiff_const.clm_comp (contDiff_const.clm_comp contDiff_id)

theorem frameSlope_contDiffAt (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (hB : IsUnit (frameTop F B)) :
    ContDiffAt ℂ ∞ (frameSlope F) B := by
  obtain ⟨u,hu⟩ := hB
  have hb : ContDiff ℂ ∞ (frameBottom F) :=
    contDiff_const.clm_comp (contDiff_const.clm_comp contDiff_id)
  have hi : ContDiffAt ℂ ∞ Ring.inverse (frameTop F B) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℂ u
  exact hb.contDiffAt.clm_comp (hi.comp B (frameTop_contDiff F).contDiffAt)

theorem frameSlope_plane (F : (GraphFrame s k)) (B : (PlaneFrameMap s k)) (hB : IsUnit (frameTop F B)) :
    graphPlane F (frameSlope F B).toLinearMap=LinearMap.range B.toLinearMap := by
  have hleft (v : (GraphHorizontal s)) : Ring.inverse (frameTop F B) (frameTop F B v)=v :=
    congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v) (Ring.inverse_mul_cancel _ hB)
  have hright (v : (GraphHorizontal s)) : frameTop F B (Ring.inverse (frameTop F B) v)=v :=
    congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v) (Ring.mul_inverse_cancel _ hB)
  ext z
  constructor
  · intro hz
    refine ⟨Ring.inverse (frameTop F B) (F z).1,?_⟩
    apply F.injective
    exact Prod.ext (hright _) hz.symm
  · rintro ⟨v,rfl⟩
    change (F (B v)).2=frameBottom F B (Ring.inverse (frameTop F B) (frameTop F B v))
    rw [hleft]
    rfl

theorem frameTop_unit (F : (GraphFrame s k)) (B : (IndependentFrame s k))
    (h : InGraphChart F (framePoint B).val) : IsUnit (frameTop F B.val) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  let e := LinearEquiv.ofInjective B.val.toLinearMap B.property
  exact h.comp e.bijective

/-- Sending an arbitrary independent frame to its actual span is continuous
for the graph topology; this connects the atlas to geometric frame families. -/
theorem framePoint_continuous : Continuous (framePoint (s := s) (k := k)) := by
  apply continuous_iff_continuousAt.mpr
  intro B
  obtain ⟨F,hF⟩ := grassmann_atlas_covers (framePoint B)
  have hu := frameTop_unit F B hF
  have htop : Continuous (fun D : (IndependentFrame s k) => frameTop F D.val) :=
    (frameTop_contDiff F).continuous.comp continuous_subtype_val
  have hev : ∀ᶠ D : (IndependentFrame s k) in 𝓝 B, IsUnit (frameTop F D.val) :=
    htop.continuousAt (Units.isOpen.mem_nhds hu)
  have hs : ContinuousAt (fun D : (IndependentFrame s k) => slopePoint F (frameSlope F D.val)) B :=
    (slopePoint_continuous F).continuousAt.comp
      ((frameSlope_contDiffAt F B.val hu).continuousAt.comp continuous_subtype_val.continuousAt)
  apply hs.congr
  filter_upwards [hev] with D hD
  apply Subtype.ext
  exact frameSlope_plane F D.val hD

end Kaplansky.ComplexGrassmann

end

section
open scoped ContDiff Manifold
open Set
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

instance grassmannChartedSpace : ChartedSpace (GraphSlope s k) (Grassmann s k) where
  atlas := Set.range grassmannChart
  chartAt P := grassmannChart (grassmann_atlas_covers P).choose
  mem_chart_source P := (grassmann_atlas_covers P).choose_spec
  chart_mem_atlas P := Set.mem_range_self (grassmann_atlas_covers P).choose

theorem grassmann_overlap_source (F G : GraphFrame s k) :
    ((grassmannChart F).symm.trans (grassmannChart G)).source=
      {A | IsUnit (graphTop F G A)} := by
  ext A
  change (A ∈ (grassmannChart F).target ∧
    (grassmannChart F).symm A ∈ (grassmannChart G).source) ↔ _
  simp only [grassmannChart_target,mem_univ,true_and,grassmannChart_source,
    grassmannChart_symm_apply,mem_ofPred_eq,slopePoint,graphPoint]
  exact inGraphChart_iff_unit F G A

instance grassmannComplexManifold : IsManifold 𝓘(ℂ, GraphSlope s k) ∞ (Grassmann s k) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨F,rfl⟩ ⟨G,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id,Set.inter_univ,Set.preimage_id,
    grassmann_overlap_source,OpenPartialHomeomorph.trans_apply] using
    grassmann_chart_transition_smooth F G

instance grassmannRealManifold : IsManifold 𝓘(ℝ, GraphSlope s k) ∞ (Grassmann s k) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨F,rfl⟩ ⟨G,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id,Set.inter_univ,Set.preimage_id,
    grassmann_overlap_source,OpenPartialHomeomorph.trans_apply] using
    (grassmann_chart_transition_smooth F G).restrict_scalars ℝ

theorem graph_slope_complex_finrank : Module.finrank ℂ (GraphSlope s k)=s*k := by
  rw [← (LinearMap.toContinuousLinearMap : (GraphMap s k) ≃ₗ[ℂ] GraphSlope s k).finrank_eq]
  exact graph_model_finrank

theorem graph_slope_real_finrank : Module.finrank ℝ (GraphSlope s k)=2*s*k := by
  rw [finrank_real_of_complex,graph_slope_complex_finrank,Nat.mul_assoc]

end Kaplansky.ComplexGrassmann

end

open Set Topology
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

/-- Every actual plane is the span of an independent frame. -/
theorem framePoint_surjective : Function.Surjective (framePoint (s := s) (k := k)) := by
  intro P
  obtain ⟨F,hF⟩ := graph_charts_cover P.val P.property
  let B : PlaneFrameMap s k :=
    F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (graphInclusion 0)
  have hB : Function.Injective B := by
    intro u v h
    have he := congrArg (fun z : Components s k => (F z).1) h
    simpa [B] using he
  refine ⟨⟨B,hB⟩,?_⟩
  apply Subtype.ext
  change LinearMap.range B.toLinearMap=P.val
  rw [← hF]
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    simp [B]
  · intro hz
    refine ⟨(F z).1,?_⟩
    apply F.injective
    have he : ((F z).1,(0 : GraphVertical k))=F z := Prod.ext rfl hz.symm
    simpa [B] using he

instance independentFrameLocallyCompact : LocallyCompactSpace (IndependentFrame s k) :=
  (ContinuousLinearMap.isOpen_injective (𝕜 := ℂ) (E := GraphHorizontal s)
    (F := Components s k)).locallyCompactSpace

instance grassmannSigmaCompact : SigmaCompactSpace (Grassmann s k) := by
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (framePoint_surjective (s := s) (k := k))]
  exact isSigmaCompact_range framePoint_continuous

instance grassmannSecondCountable : SecondCountableTopology (Grassmann s k) :=
  ChartedSpace.secondCountable_of_sigmaCompact (GraphSlope s k) (Grassmann s k)

/-- The graph atlas has a countable subcover of actual planes, providing the
countability needed for the lower-dimensional image argument. -/
theorem exists_countable_graph_cover : ∃ c : Set (GraphFrame s k), c.Countable ∧
    ∀ P : Grassmann s k, ∃ F ∈ c, InGraphChart F P.val := by
  have hcover : (univ : Set (Grassmann s k)) ⊆ ⋃ F : GraphFrame s k, (grassmannChart F).source := by
    intro P _
    obtain ⟨F,hF⟩ := grassmann_atlas_covers P
    exact mem_iUnion.mpr ⟨F,hF⟩
  obtain ⟨c,hc,hcov⟩ := isLindelof_univ.elim_countable_subcover
    (fun F : GraphFrame s k => (grassmannChart F).source) (fun F => (grassmannChart F).open_source) hcover
  refine ⟨c,hc,fun P => ?_⟩
  simpa only [Set.mem_iUnion,exists_prop,grassmannChart_source,Set.mem_ofPred_eq] using hcov (mem_univ P)

end Kaplansky.ComplexGrassmann

end

end OAI
