import OAI.Analysis.CircleDomains.Reflection.ActualPhaseReflection

namespace OAI

/-! Joint extraction identifies the reflected collar limit with the
actual normalized conformal limit on the original domain. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.exists_joint_limit (P:PhaseCollar C i) (t:ℕ→ℕ) :
    ∃s:ℕ→ℕ, ∃F G:ℂ→ℂ, StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => P.reflected (t (s n))) F atTop
        (symmetricCircleAnnulus P.radius) ∧
      TendstoLocallyUniformlyOn (fun n (z:ℂ) => finiteCoord
        (cumulativeMap C (cyclicSchedule m) (visitTime (t (s n)) i+1) (z:Sphere)))
        G atTop C.planeRegion ∧
      DifferentiableOn ℂ F (symmetricCircleAnnulus P.radius) ∧
      IsPrincipalNormalized (extendAtInfinity G) ∧
      IsConformalEquivalence (extendAtInfinity G) C.region (extendAtInfinity G '' C.region) ∧
      (∀z∈symmetricCircleAnnulus P.radius,1<‖z‖ → F z=G (P.coordinate z)) ∧
      InjOn F (symmetricCircleAnnulus P.radius∩{z | 1<‖z‖}) := by
  obtain ⟨a,F,ha,hFa,hFd⟩ := P.exists_reflected_limit t
  obtain ⟨b,G,hb,hGb,hGd,hGi,hGn⟩ := exists_circularization_normal_limit_along C (cyclicSchedule m)
    (fun n => visitTime (t (a n)) i+1)
  have hF : TendstoLocallyUniformlyOn (fun n => P.reflected (t (a (b n)))) F atTop
      (symmetricCircleAnnulus P.radius) := by
    intro V hV z hz
    obtain ⟨W,hW,he⟩ := hFa V hV z hz
    exact ⟨W,hW,hb.tendsto_atTop.eventually he⟩
  have heq (z:ℂ) (hz:z∈symmetricCircleAnnulus P.radius) (hzo:1<‖z‖) :
      F z=G (P.coordinate z) := by
    have hfz := hF.tendsto_at hz
    have hgz := hGb.tendsto_at (P.exterior_source z hz hzo)
    apply tendsto_nhds_unique hfz
    exact hgz.congr' (Eventually.of_forall fun n =>
      (P.reflected_agrees (t (a (b n))) hz hzo).symm)
  refine ⟨a ∘ b,F,G,ha.comp hb,hF,hGb,hFd,
    isPrincipalNormalized_extendAtInfinity hGn,C.conformal_limit hGd hGi hGn,heq,?_⟩
  intro z hz w hw hzw
  apply P.injective hz.1 hw.1
  apply hGi (P.exterior_source z hz.1 hz.2) (P.exterior_source w hw.1 hw.2)
  rw [←heq z hz.1 hz.2,←heq w hw.1 hw.2]
  exact hzw

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
