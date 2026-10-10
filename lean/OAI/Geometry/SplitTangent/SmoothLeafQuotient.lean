import Mathlib
import OAI.Geometry.SplitTangent.ActualQuotientCharts
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SwappedProductChart

namespace OAI

/-! Smooth Leaf Quotient. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

def smoothLeafLocus : Set (L.CompactLeafSpace e hRC hdim) :=
  {q | ∃ (i : X.Carrier) (D : L.QuotientChartData e hRC hdim i),q∈D.chart.source}

lemma smoothLeafLocus_isOpen : IsOpen (L.smoothLeafLocus e hRC hdim) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨i,D,hq⟩
  exact Filter.mem_of_superset (D.chart.open_source.mem_nhds hq) (fun r hr => ⟨i,D,hr⟩)

include M in
lemma smoothLeafLocus_dense : Dense (L.smoothLeafLocus e hRC hdim) := by
  have hd := (L.regularLeafPairs_dense M e hRC hdim).preimage (L.isOpenMap_leafPair M e hRC hdim)
  have hsub : L.leafPair M e hRC hdim ⁻¹' L.regularLeafPairs M e hRC hdim ⊆
      L.leafQuotient e hRC hdim ⁻¹' L.smoothLeafLocus e hRC hdim := by
    intro x hx
    obtain ⟨D,hD⟩ := L.exists_quotientChartData_of_regular e hRC hdim M hx
    exact ⟨x,D,hD⟩
  intro q
  obtain ⟨x,rfl⟩ := L.surjective_leafQuotient e hRC hdim q
  apply closure_mono (image_preimage_subset (L.leafQuotient e hRC hdim)
    (L.smoothLeafLocus e hRC hdim))
  exact (image_closure_subset_closure_image (L.continuous_leafQuotient e hRC hdim))
    ⟨x,hd.mono hsub x,rfl⟩

namespace QuotientChartData
variable {L e hRC hdim} {i : X.Carrier} (D : L.QuotientChartData e hRC hdim i)

lemma transition_holomorphic {j : X.Carrier} (D' : L.QuotientChartData e hRC hdim j)
    {b : S.SecondModel i} (hb : b∈(D.chart.symm.trans D'.chart).source) :
    ContDiffAt ℂ ω (D'.chart ∘ D.chart.symm) b := by
  have ht : (D.a,b)∈(L.chart i).chart.target := D.rectangle ⟨D.mem_U,hb.1⟩
  have hi := ((L.chart i).inverse_holomorphicAt ht).comp b
    (contMDiffAt_const.prodMk_space contMDiffAt_id)
  exact ((D'.chart_comp_quotient_contMDiffAt hb.2).comp b hi).contDiffAt

variable (x₀ : X.Carrier)
def quotientRankEquiv (_D : L.QuotientChartData e hRC hdim i) : S.SecondModel i ≃L[ℂ] (Fin (Module.finrank ℂ (S.second x₀)) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    have hi := (L.chart i).swap.first_finrank (by
      rw [AlignedProductChart.swap_source]
      exact L.mem_source i)
    have he := M.first_rank_eq i x₀
    rw [S.swap_first] at hi he
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hi.symm.trans he)

def normalized : OpenPartialHomeomorph (L.CompactLeafSpace e hRC hdim)
    (Fin (Module.finrank ℂ (S.second x₀)) → ℂ) :=
  D.chart.trans (D.quotientRankEquiv M x₀).toHomeomorph.toOpenPartialHomeomorph

lemma normalized_source : (D.normalized M x₀).source=D.chart.source := by
  ext q
  exact ⟨fun h => h.1,fun h => ⟨h,Set.mem_univ _⟩⟩

lemma normalized_comp_quotient_contMDiffAt {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈(D.normalized M x₀).source) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ) ω
      (D.normalized M x₀ ∘ L.leafQuotient e hRC hdim) x :=
  (D.quotientRankEquiv M x₀).contDiff.contMDiff.contMDiffAt.comp x
    (D.chart_comp_quotient_contMDiffAt hx.1)

def localSection (a : Fin (Module.finrank ℂ (S.second x₀)) → ℂ) : X.Carrier :=
  (L.chart i).chart.symm (D.a,(D.quotientRankEquiv M x₀).symm a)

lemma normalized_inverse (a : Fin (Module.finrank ℂ (S.second x₀)) → ℂ) :
    (D.normalized M x₀).symm a=L.leafQuotient e hRC hdim (D.localSection M x₀ a) := rfl

lemma localSection_holomorphic {a : Fin (Module.finrank ℂ (S.second x₀)) → ℂ}
    (ha : a∈(D.normalized M x₀).target) :
    ContMDiffAt 𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ) (ModelWithCorners X) ω
      (D.localSection M x₀) a := by
  apply ((L.chart i).inverse_holomorphicAt (D.rectangle (show (D.a,(D.quotientRankEquiv M x₀).symm a)∈D.U ×ˢ D.V from ⟨D.mem_U,ha.2⟩))).comp a
  exact contMDiffAt_const.prodMk_space (D.quotientRankEquiv M x₀).symm.contDiff.contMDiff.contMDiffAt

lemma normalized_transition_holomorphic {j : X.Carrier} (D' : L.QuotientChartData e hRC hdim j)
    {a : Fin (Module.finrank ℂ (S.second x₀)) → ℂ}
    (ha : a∈((D.normalized M x₀).symm.trans (D'.normalized M x₀)).source) :
    ContDiffAt ℂ ω (D'.normalized M x₀ ∘ (D.normalized M x₀).symm) a := by
  have hi := D.localSection_holomorphic M x₀ ha.1
  have hf := D'.normalized_comp_quotient_contMDiffAt M x₀
    (show L.leafQuotient e hRC hdim (D.localSection M x₀ a)∈(D'.normalized M x₀).source from ha.2)
  exact (hf.comp a hi).contDiffAt

end QuotientChartData
end SplitTangent.LeafJetAtlas

end

end OAI
