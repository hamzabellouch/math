import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanGraphGeometry
import OAI.Analysis.CircleDomains.Sobolev.SmoothRealLift

namespace OAI

/-! The retained mean branches project to the actual physical circle
coordinate. Its smoothness upgrades those continuous branches to smooth
real functions on the physical patch, as required by terminal filling. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem SmoothMeanPeriodData.branch_physical_projection
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (i : Q.Index) {z : ℂ} (hz : (z : Sphere) ∈ G) (hi : π (z : Sphere) ∈ Q.patch i) :
    (Q.branch i (π (z : Sphere)) : UnitAddCircle) = Q.physical z := by
  have hs : π (z : Sphere) ∈ S := Q.patch_closure i (subset_closure hi)
  rw [Q.branch_value i _ hi, Q.physical_value z hz hs, AddCircle.coe_add]
  congr 1
  rw [← diskMeanCircle_projection hsch hsep K hK hKS η,
    upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (Q.angle i) (h1 _ hs)),
    logarithmicCutChart_projection (Q.angle i) (h0 _ hs)]

 theorem SmoothMeanPeriodData.branch_physical_smooth
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) {b : Sphere}
    {π : Sphere → Sphere} (hπ : Continuous π)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π) (i : Q.Index) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => Q.branch i (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' Q.patch i) := by
  have hO : IsOpen (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' Q.patch i) :=
    (hG.preimage OnePoint.continuous_coe).inter
      ((Q.patch_open i).preimage (hπ.comp OnePoint.continuous_coe))
  apply contDiffOn_real_lift hO
    (fun z hz => Q.physical_smooth z
      ⟨hz.1, Q.patch_closure i (subset_closure hz.2)⟩)
    (Q.branch_smooth i).continuousOn
  intro z hz
  exact Q.branch_physical_projection hsch hsep K hK hKS η F h0 h1 i hz.1 hz.2

end CircleDomainRigidity

end

end OAI
