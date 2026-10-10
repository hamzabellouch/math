import OAI.Analysis.StructuralCrouzeix.OptimizerAssembly
import OAI.Analysis.StructuralCrouzeix.SharedMaximum
import OAI.Analysis.StructuralCrouzeix.ClosedSide
import OAI.Analysis.StructuralCrouzeix.OrientBoundary
import OAI.Analysis.StructuralCrouzeix.ExteriorSupport

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma IsAdmissible.compact_closure {U : Set ℂ} (hU : IsAdmissible U) :
    IsCompact (closure U) :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hU.bounded.closure⟩

lemma IsAdmissible.sided_boundary {U : Set ℂ} (hU : IsAdmissible U) :
    ∀ p ∈ frontier U, LocalAnalyticBoundary U p := by
  intro p hp
  exact RegularAnalyticBoundaryAt.orient hU.isOpen hU.convex hU.nonempty hp
    (hU.regular p hp)

theorem IsAdmissible.coordinates {U : Set ℂ} (hU : IsAdmissible U) :
    (∀ a ∈ U, Nonempty (DiskCoordinate U a)) ∧ Nonempty (ExteriorCoordinate U) := by
  constructor
  · intro a ha
    exact convex_analytic_interior_coordinate hU.isOpen hU.convex hU.compact_closure
      ha hU.sided_boundary
  · obtain ⟨a,ha⟩ := hU.nonempty
    exact convex_analytic_exterior_coordinate hU.isOpen hU.convex hU.compact_closure
      ha hU.sided_boundary

def bundleDomain {U : Set ℂ} (hU : IsAdmissible U) (a : ℂ) (ha : a ∈ U)
    (f : DiskCoordinate U a) (G : ExteriorCoordinate U) : AdmissibleDomain where
  domain := U
  isOpen := hU.isOpen
  convex := hU.convex
  compact_closure := hU.compact_closure
  base := a
  base_mem := ha
  interior := f
  exterior := G
  support := convex_exteriorCoordinate_support hU.isOpen hU.convex hU.nonempty G

lemma bundleDomain_boundaryPoint {U : Set ℂ} (hU : IsAdmissible U)
    (a : ℂ) (ha : a ∈ U) (f : DiskCoordinate U a) (G : ExteriorCoordinate U)
    (t : UnitAddCircle) :
    (bundleDomain hU a ha f G).G (t.toCircle : ℂ) = boundaryPoint G t := rfl

lemma bundleDomain_maximum {U : Set ℂ} (hU : IsAdmissible U)
    (a : ℂ) (ha : a ∈ U) (f : DiskCoordinate U a) (G : ExteriorCoordinate U)
    {m : ℕ} (v : ℂ → Matrix (Fin m) (Fin m) ℂ) :
    (bundleDomain hU a ha f G).analyticRangeMaximum v = analyticSupNorm U v := rfl

theorem fullEndpoint : FullEndpoint := by
  intro U hU
  obtain ⟨hinterior,hexterior⟩ := hU.coordinates
  refine ⟨hinterior,hexterior,?_⟩
  intro a ha f G n hn A hW
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let D := bundleDomain hU a ha f G
  have hWD : numericalRange A ⊆ D.domain := hW
  obtain ⟨hstrict,κ,hκlo,hκhi,hattained,hall⟩ := optimal_metric_bundle D A hWD
  refine ⟨hstrict,κ,hκlo,hκhi,hattained,?_⟩
  intro H hH
  obtain ⟨hp,hu,heval,hcontract,hstable,hcondition,hminimal⟩ := hall H hH
  refine ⟨hp,hu,heval,hcontract,hstable,hcondition,hminimal,?_⟩
  obtain ⟨Λ,hpos,hmass,hrep⟩ := D.common_positiveDensity_maximum_for_metric A H hWD hH.1
  refine ⟨Λ,(fun t => Matrix.nonneg_iff_posSemidef.mp (hpos t)),hmass,?_⟩
  intro m hm v hv
  obtain ⟨he,hb⟩ := hrep m hm v hv
  constructor
  · change completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
      ∫ t, Λ t ⊗ₖ v (boundaryPoint G t) ∂AddCircle.haarAddCircle
    change completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
      ∫ t, Λ t ⊗ₖ v ((bundleDomain hU a ha f G).G t.toCircle)
        ∂AddCircle.haarAddCircle at he
    simpa only [bundleDomain_boundaryPoint] using he
  · change ‖completeAnalyticEval A v‖ ≤
      (‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖) * analyticSupNorm U v at hb
    rwa [hcondition] at hb

end StructuralCrouzeix
end

end OAI
