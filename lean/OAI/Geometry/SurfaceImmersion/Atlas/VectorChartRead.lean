import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import OAI.Geometry.SurfaceImmersion.Geometry.SupportJetEquality

namespace OAI

/-! Actual global smooth chart representatives. On the original phase
support they preserve every derivative, including at the support boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma chartWeight_tsupport (i : A.centers) :
    tsupport (A.chartWeight i) = (A.chartWeightCompact i : Set JetPolynomial.Base) := by
  apply Subset.antisymm (A.supportedChartWeight i).tsupport_subset
  rintro x ⟨p,hp,rfl⟩
  have hc : ContinuousAt (chart (i : M)) p :=
    ((chart (i : M)).continuousOn p (A.weight_support i hp)).continuousAt
      ((chart (i : M)).open_source.mem_nhds (A.weight_support i hp))
  have hh := mem_closure_image hc hp
  apply closure_mono _ hh
  rintro y ⟨q,hq,rfl⟩
  change A.weight i q ≠ 0 at hq
  have hs := A.weight_support i (subset_tsupport (A.weight i) hq)
  change A.chartWeight i (chart (i : M) q) ≠ 0
  simpa only [chartWeight,indicator_of_mem ((chart (i : M)).map_source hs),
    (chart (i : M)).left_inv hs] using hq

def vectorChartRead (i : A.centers) (F : M → V) : JetPolynomial.Base → V :=
  localize (i : M) (A.outer i) F

def vectorPlaneRead (i : A.centers) (F : M → V) : SmallModes.Base → V :=
  A.vectorChartRead i F ∘ planeCoordinateIsometry.symm

lemma vectorChartRead_smooth (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) : ContDiff ℝ ∞ (A.vectorChartRead i F) :=
  localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) hF

lemma vectorPlaneRead_smooth (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) : ContDiff ℝ ∞ (A.vectorPlaneRead i F) :=
  (A.vectorChartRead_smooth i hF).comp planeCoordinateIsometry.symm.contDiff

lemma vectorChartRead_on_support (i : A.centers) (F : M → V)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i F x = F ((chart (i : M)).symm x) := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [vectorChartRead,localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp,
    (chart (i : M)).left_inv (A.weight_support i hp),one_pow,one_smul]

lemma vectorChartRead_jets (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) (m : ℕ)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (A.vectorChartRead i F) x =
      iteratedFDeriv ℝ m (F ∘ (chart (i : M)).symm) x := by
  have hk : tsupport (A.chartWeight i) ⊆ (chart (i : M)).target := by
    rw [A.chartWeight_tsupport]
    rintro y ⟨p,hp,rfl⟩
    exact (chart (i : M)).map_source (A.weight_support i hp)
  have hg : ContDiffOn ℝ ∞ (F ∘ (chart (i : M)).symm) (chart (i : M)).target :=
    (hF.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  apply iteratedFDeriv_eq_on_tsupport (A.chartWeight_smooth i).continuous
    (chart (i : M)).open_target hk (A.vectorChartRead_smooth i hF).contDiffOn hg
    (fun y hy => A.vectorChartRead_on_support i F (A.chartWeight_tsupport i ▸ hy)) m
  rwa [A.chartWeight_tsupport]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
