import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SmoothLeafQuotient

namespace OAI

/-! Smooth Leaf Manifold. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

def smoothLeafOpen : Opens (L.CompactLeafSpace e hRC hdim) :=
  ⟨L.smoothLeafLocus e hRC hdim,L.smoothLeafLocus_isOpen e hRC hdim⟩

include M in
lemma smoothLeafOpen_nonempty : Nonempty (L.smoothLeafOpen e hRC hdim) :=
  (L.smoothLeafLocus_dense M e hRC hdim).nonempty.to_subtype

namespace SmoothLeafManifold
variable {L e hRC hdim}

def selectedChart (q : L.smoothLeafOpen e hRC hdim) :
    Σi,L.QuotientChartData e hRC hdim i :=
  ⟨q.property.choose,q.property.choose_spec.choose⟩

lemma selectedChart_mem (q : L.smoothLeafOpen e hRC hdim) :
    q.val∈(selectedChart q).2.chart.source := q.property.choose_spec.choose_spec

variable (x₀ : X.Carrier)
def chart (q : L.smoothLeafOpen e hRC hdim) :
    OpenPartialHomeomorph (L.smoothLeafOpen e hRC hdim)
      (Fin (Module.finrank ℂ (S.second x₀)) → ℂ) :=
  ((selectedChart q).2.normalized M x₀).subtypeRestr (L.smoothLeafOpen_nonempty M e hRC hdim)

lemma chart_mem (q : L.smoothLeafOpen e hRC hdim) : q∈(chart M x₀ q).source := by
  rw [chart,OpenPartialHomeomorph.subtypeRestr_source]
  change q.val∈((selectedChart q).2.normalized M x₀).source
  rw [QuotientChartData.normalized_source]
  exact selectedChart_mem q

lemma chart_source (q : L.smoothLeafOpen e hRC hdim) :
    (chart M x₀ q).source=Subtype.val ⁻¹' ((selectedChart q).2.normalized M x₀).source :=
  OpenPartialHomeomorph.subtypeRestr_source _ _

lemma chart_inverse_val (q : L.smoothLeafOpen e hRC hdim)
    {a : Fin (Module.finrank ℂ (S.second x₀)) → ℂ} (ha : a∈(chart M x₀ q).target) :
    ((chart M x₀ q).symm a).val=((selectedChart q).2.normalized M x₀).symm a :=
  OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ ha

lemma transition_holomorphic (q r : L.smoothLeafOpen e hRC hdim)
    {a : Fin (Module.finrank ℂ (S.second x₀)) → ℂ}
    (ha : a∈((chart M x₀ q).symm.trans (chart M x₀ r)).source) :
    ContDiffAt ℂ ω (chart M x₀ r ∘ (chart M x₀ q).symm) a := by
  have h₁ : a∈((selectedChart q).2.normalized M x₀).target :=
    OpenPartialHomeomorph.subtypeRestr_target_subset _ _ ha.1
  have h₂ : ((selectedChart q).2.normalized M x₀).symm a∈
      ((selectedChart r).2.normalized M x₀).source := by
    rw [←chart_inverse_val M x₀ q ha.1]
    have hr : (chart M x₀ q).symm a∈(chart M x₀ r).source := ha.2
    rw [chart_source] at hr
    exact hr
  have hh := (selectedChart q).2.normalized_transition_holomorphic M x₀
    (selectedChart r).2 ⟨h₁,h₂⟩
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chart M x₀ q).open_target.mem_nhds ha.1] with b hb
  change (selectedChart r).2.normalized M x₀ (((chart M x₀ q).symm b).val)=_
  rw [chart_inverse_val M x₀ q hb]
  rfl

@[instance_reducible]
def chartedSpace : ChartedSpace (Fin (Module.finrank ℂ (S.second x₀)) → ℂ)
    (L.smoothLeafOpen e hRC hdim) where
  atlas := range (chart M x₀)
  chartAt := chart M x₀
  mem_chart_source := chart_mem M x₀
  chart_mem_atlas q := ⟨q,rfl⟩

lemma isManifold : letI := chartedSpace (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀;
    IsManifold 𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ) ω (L.smoothLeafOpen e hRC hdim) := by
  let := chartedSpace (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀
  apply isManifold_of_contDiffOn
  rintro c d ⟨q,rfl⟩ ⟨r,rfl⟩ a ha
  have ha' : a∈((chart M x₀ q).symm.trans (chart M x₀ r)).source := ha.1
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_id,Function.id_comp,OpenPartialHomeomorph.coe_trans] using
    (transition_holomorphic M x₀ q r ha').contDiffWithinAt

 

def manifold : ComplexManifold.{u} where
  dim := Module.finrank ℂ (S.second x₀)
  Carrier := L.smoothLeafOpen e hRC hdim
  charts := chartedSpace M x₀
  holomorphicAtlas := isManifold M x₀

end SmoothLeafManifold
end SplitTangent.LeafJetAtlas

end

end OAI
