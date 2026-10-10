import OAI.Analysis.CircleDomains.Uniformization.MarkedJointPhaseLimit
import OAI.Analysis.CircleDomains.Topology.NondegeneratePhaseCircle
import OAI.Analysis.CircleDomains.Topology.SymmetricAnnulusConnected
import OAI.Analysis.CircleDomains.Selection.AnnularOuterNonconstant
import OAI.Analysis.CircleDomains.Uniformization.HurwitzUnivalentProof

namespace OAI

/-! The actual reflected phase limits are univalent across the original
boundary and have nonzero limiting circle radius. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.limit_injective (P:PhaseCollar C i) {s:ℕ→ℕ} {F:ℂ→ℂ}
    (hl:TendstoLocallyUniformlyOn (fun n => P.reflected (s n)) F atTop
      (symmetricCircleAnnulus P.radius))
    (hi:InjOn F (symmetricCircleAnnulus P.radius∩{z | 1<‖z‖})) :
    InjOn F (symmetricCircleAnnulus P.radius) := by
  apply hurwitzUnivalentLimit _ _ _ (isOpen_symmetricCircleAnnulus P.radius)
    (isConnected_symmetricCircleAnnulus P.radius_gt)
    (Eventually.of_forall (fun n => ⟨P.reflected_holomorphic (s n),P.reflected_injective (s n)⟩)) hl
  exact not_constant_of_injective_outer_annulus P.radius_gt hi

structure RegularPhaseLimit (P:PhaseCollar C i) where
  subsequence : ℕ→ℕ
  boundaryMap : ℂ→ℂ
  map : ℂ→ℂ
  center : ℂ
  radius : ℝ
  strictMono : StrictMono subsequence
  radius_pos : 0<radius
  centers_tendsto : Tendsto (fun n => selectedCenter C (cyclicSchedule m)
    (visitTime (subsequence n) i)) atTop (𝓝 center)
  radii_tendsto : Tendsto (fun n => selectedRadius C (cyclicSchedule m)
    (visitTime (subsequence n) i)) atTop (𝓝 radius)
  boundary_tendsto : TendstoLocallyUniformlyOn (fun n => P.reflected (subsequence n))
    boundaryMap atTop (symmetricCircleAnnulus P.radius)
  map_tendsto : TendstoLocallyUniformlyOn (fun n (z:ℂ) => finiteCoord
    (cumulativeMap C (cyclicSchedule m) (visitTime (subsequence n) i+1) (z:Sphere)))
    map atTop C.planeRegion
  holomorphic : DifferentiableOn ℂ boundaryMap (symmetricCircleAnnulus P.radius)
  injective : InjOn boundaryMap (symmetricCircleAnnulus P.radius)
  derivative_ne : ∀z∈symmetricCircleAnnulus P.radius,deriv boundaryMap z≠0
  normalized : IsPrincipalNormalized (extendAtInfinity map)
  conformal : IsConformalEquivalence (extendAtInfinity map) C.region (extendAtInfinity map '' C.region)
  agrees : ∀z∈symmetricCircleAnnulus P.radius,1<‖z‖ → boundaryMap z=map (P.coordinate z)
  circle : ∀z∈symmetricCircleAnnulus P.radius,‖z‖=1 → ‖boundaryMap z-center‖=radius

lemma PhaseCollar.regularPhaseLimit_nonempty (P:PhaseCollar C i) :
    Nonempty (RegularPhaseLimit P) := by
  obtain ⟨s,F,G,a,ρ,hs,hρ,hc,hr,hF,hG,hd,hn,hg,he,hi,hcircle⟩ := P.exists_marked_joint_limit
  have hpos := circle_radius_pos_of_injective_outer P.radius_gt hρ hd hi hcircle
  have hfi := P.limit_injective hF hi
  exact ⟨{
    subsequence := s
    boundaryMap := F
    map := G
    center := a
    radius := ρ
    strictMono := hs
    radius_pos := hpos
    centers_tendsto := hc
    radii_tendsto := hr
    boundary_tendsto := hF
    map_tendsto := hG
    holomorphic := hd
    injective := hfi
    derivative_ne := fun z hz => holomorphicInjOn_deriv_ne_zero
      (isOpen_symmetricCircleAnnulus P.radius) hd hfi hz
    normalized := hn
    conformal := hg
    agrees := he
    circle := hcircle }⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
