import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiRough
import OAI.Geometry.PrescribedRicci.CalabiTensorAlgebra
import OAI.Geometry.PrescribedRicci.ContractedBochner
import OAI.Geometry.PrescribedRicci.MatrixWirtinger

namespace OAI

/-! Calabi Bochner. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff MatrixOrder
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "TI" => TensorIndex (Fin d)

def calabiEnergy (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : ℝ :=
  (tensorEnergy (g.matrix q z)⁻¹ (g.calabiMetric q z) (barVector (g.calabiTensor q) z)).re+
  (tensorEnergy (g.matrix q z)⁻¹.transpose (g.calabiMetric q z)
    (covHol (g.calabiConnection q) (g.calabiTensor q) z)).re

def calabiRoughTerm (g : KaehlerMetric A) (q : Fin A.count) (z : Coordinates d) : TI → ℂ :=
  fun i => (-(g.matrix q z)⁻¹*holDerivative (g.curvatureRicci q) z i.1+
    ((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z i.1) i.2.1 i.2.2

lemma calabiEnergy_nonneg (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) : 0 ≤ g.calabiEnergy q z := by
  unfold calabiEnergy
  exact add_nonneg (tensorEnergy_nonneg (g.positive q z hz).inv.posSemidef
    (g.calabiMetric_posDef q hz).posSemidef _)
    (tensorEnergy_nonneg (g.positive q z hz).inv.transpose.posSemidef
      (g.calabiMetric_posDef q hz).posSemidef _)

lemma calabiNorm_laplacian (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ((g.matrix q z)⁻¹*PotentialKaehler.potentialMatrix (g.calabiNorm q) z).trace.re =
      g.calabiEnergy q z+
      2*(hermPair (g.calabiMetric q z) (g.calabiTensor q z) (g.calabiRoughTerm q z)).re+
      (hermPair (g.calabiMetric q z) (g.calabiTensor q z)
        ((tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z)))*ᵥ
          g.calabiTensor q z)).re := by
  have h := contracted_bochners_identity (A.chart q).open_target hz
    (fun y hy => g.calabiMetric_smooth q hy) (fun y hy => g.calabiConnection_smooth q hy)
    (fun y hy => g.calabiTensor_smooth q hy)
    (fun y hy => (g.calabiMetric_posDef q hy).isHermitian)
    (fun y hy => g.calabiMetric_hol q hy) (fun y hy => g.calabiMetric_bar q hy)
    (g.matrix q z)⁻¹ (g.positive q z hz).inv.isHermitian
  rw [g.calabiTensor_rough q hz,g.calabiConnection_contracted_curvature q hz] at h
  exact h

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
