import OAI.Analysis.CircleDomains.Rigidity.MatchedCommonPoints
import OAI.Analysis.CircleDomains.Rigidity.RemovableAreaZero
import OAI.Analysis.CircleDomains.Sobolev.RealCoordinateLines

namespace OAI

/-! The common point set is contained in the removable boundary and
therefore has null intersections with almost every coordinate line. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem commonPointPlane_subset_frontier
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) : (z : Sphere) ∈ frontier G := by
  have hs := (D.commonPointPlane_singletons hG hinf hf hH hinf' hz).1
  have hproper : Gᶜ ≠ univ := by
    intro he
    exact (show OnePoint.infty ∈ Gᶜ from he.symm ▸ mem_univ _) hinf
  obtain ⟨p,hp,hpf⟩ := component_meets_frontier hG.1.isClosed_compl hproper hz.1
  have hpz : p = (z : Sphere) := mem_singleton_iff.mp (hs ▸ hp)
  simpa only [frontier_compl,hpz] using hpf

 theorem commonPointPlane_line_null
    (hprincipal : PrincipalRealBeltrami)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G)) (i : Fin 2) :
    ∀ᵐ y ∂volume, volume {x | complexCoordinateLine i y x ∈ D.commonPointPlane} = 0 := by
  have hn : OnePoint.infty ∈ (frontier G)ᶜ := by
    intro hx
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hG.1) hx hinf
  have hvol := removable_complement_volume_zero hprincipal isClosed_frontier.isOpen_compl hn
    (by simpa only [compl_compl] using hrem)
  have havoid : ∀ᵐ z ∂volume, planeSphere z ∉ frontier G := by
    apply ae_iff.mpr
    convert hvol using 1
    congr 1
  have hc : ∀ᵐ z ∂volume, Complex.equivRealProdCLM.symm z ∉ D.commonPointPlane := by
    have hmp := euclideanPlaneCoordinates_symm_measurePreserving
    filter_upwards [hmp.quasiMeasurePreserving.ae havoid] with z hz
    intro hcommon
    apply hz
    convert D.commonPointPlane_subset_frontier hG hinf hf hH hinf' hcommon using 1
    simp only [planeSphere,complexPlaneCoordinates,ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  filter_upwards [ae_ae_realCoordinateLine hc i] with y hy
  simpa only [not_not,complexCoordinateLine] using (ae_iff.mp hy)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
