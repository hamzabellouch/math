import OAI.Analysis.CircleDomains.Uniformization.InjectivePhaseLimit
import OAI.Analysis.CircleDomains.Modulus.HolomorphicStrictNorm
import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflectionSides

namespace OAI

/-! The two sides of the limiting analytic boundary keep their exact
inside/outside assignment. The bounds are passed from the actual finite maps. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}
variable {P:PhaseCollar C i} (L:RegularPhaseLimit P)

lemma RegularPhaseLimit.outer_le {z:ℂ} (hz:z∈symmetricCircleAnnulus P.radius)
    (hzo:1≤‖z‖) : L.radius≤‖L.boundaryMap z-L.center‖ := by
  apply le_of_tendsto_of_tendsto L.radii_tendsto
    (((L.boundary_tendsto.tendsto_at hz).sub L.centers_tendsto).norm)
  exact Eventually.of_forall (fun n => by
    change selectedRadius C (cyclicSchedule m) (visitTime (L.subsequence n) i)≤
      ‖P.reflected (L.subsequence n) z-selectedCenter C (cyclicSchedule m) (visitTime (L.subsequence n) i)‖
    rw [PhaseCollar.reflected,circleReflectionExtension_outer
      (selectedRadius_pos C (cyclicSchedule m) (visitTime (L.subsequence n) i)) hzo]
    exact P.outside _ z hz hzo)

lemma RegularPhaseLimit.inner_le {z:ℂ} (hz:z∈symmetricCircleAnnulus P.radius)
    (hzi:‖z‖<1) : ‖L.boundaryMap z-L.center‖≤L.radius := by
  apply le_of_tendsto_of_tendsto
    (((L.boundary_tendsto.tendsto_at hz).sub L.centers_tendsto).norm) L.radii_tendsto
  exact Eventually.of_forall (fun n => circleReflectionExtension_inside_norm_le
    (selectedRadius_pos C (cyclicSchedule m) (visitTime (L.subsequence n) i))
    (fun _ hw => symmetricCircleAnnulus_ne_zero (zero_lt_one.trans P.radius_gt) hw)
    (fun _ hw => symmetricCircleAnnulus_reflection (zero_lt_one.trans P.radius_gt) hw)
    (P.outside (L.subsequence n)) hz hzi)

lemma RegularPhaseLimit.outer_strict {z:ℂ} (hz:z∈symmetricCircleAnnulus P.radius)
    (hzo:1<‖z‖) : L.radius<‖L.boundaryMap z-L.center‖ := by
  let V := symmetricCircleAnnulus P.radius∩{z:ℂ | 1<‖z‖}
  have hV : IsOpen V := (isOpen_symmetricCircleAnnulus P.radius).inter
    (isOpen_lt continuous_const continuous_norm)
  exact holomorphicInjOn_norm_gt hV (L.holomorphic.mono inter_subset_left)
    (L.injective.mono inter_subset_left) L.radius_pos
    (fun w hw => L.outer_le hw.1 hw.2.le) ⟨hz,hzo⟩

lemma RegularPhaseLimit.inner_strict {z:ℂ} (hz:z∈symmetricCircleAnnulus P.radius)
    (hzi:‖z‖<1) : ‖L.boundaryMap z-L.center‖<L.radius := by
  let V := symmetricCircleAnnulus P.radius∩{z:ℂ | ‖z‖<1}
  have hV : IsOpen V := (isOpen_symmetricCircleAnnulus P.radius).inter
    (isOpen_lt continuous_norm continuous_const)
  exact holomorphicInjOn_norm_lt hV (L.holomorphic.mono inter_subset_left)
    (L.injective.mono inter_subset_left)
    (fun w hw => L.inner_le hw.1 hw.2) ⟨hz,hzi⟩

lemma RegularPhaseLimit.boundary_iff {z:ℂ} (hz:z∈symmetricCircleAnnulus P.radius) :
    ‖L.boundaryMap z-L.center‖=L.radius ↔ ‖z‖=1 := by
  refine ⟨?_,L.circle z hz⟩
  intro he
  rcases lt_trichotomy ‖z‖ 1 with h|h|h
  · exact False.elim ((ne_of_lt (L.inner_strict hz h)) he)
  · exact h
  · exact False.elim ((ne_of_gt (L.outer_strict hz h)) he)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
