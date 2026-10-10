import OAI.Analysis.CircleDomains.Topology.AnalyticBoundaryGerms
import OAI.Analysis.CircleDomains.Topology.BoundaryGlobalInjectivity
import OAI.Analysis.CircleDomains.Reflection.ClosedExteriorBoundaryValues

namespace OAI

/-! The actual closed-exterior extension is globally injective, including
its entire analytic Jordan boundary. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma analytic_jordan_closed_exterior_injective {H : ℂ ≃ₜ ℂ}
    (hH : IsAnalyticJordanCap H) {f : Sphere → Sphere} {d : ℂ} {s : ℝ}
    (hs : 0<s) (hf : IsConformalEquivalence f (closedTerminalCap H)ᶜ
      ((((↑) : ℂ → Sphere) '' closedBall d s)ᶜ)) :
    let A := (closure (jordanInterior H))ᶜ
    let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))
    InjOn (extendFrom A g) (closure A) := by
  dsimp only
  let A := (closure (jordanInterior H))ᶜ
  let g := fun z : ℂ => finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))
  let E := extendFrom A g
  let K := frontier (jordanInterior H)
  change InjOn E (closure A)
  have hnorm := hf.trans (isConformalEquivalence_exteriorDiskNormalization d hs)
  have hzU {z:ℂ} (hz:z∈A) : (z:Sphere)∈(closedTerminalCap H)ᶜ := by
    rintro ⟨w,hw,he⟩
    exact hz (OnePoint.coe_injective he ▸ hw)
  have hu : ∀z∈A,‖g z‖<1 := by
    intro z hz
    obtain ⟨w,hw,he⟩ := hnorm.2.1 (hzU hz)
    change (w : Sphere)=exteriorDiskNormalization d s hs (f (z : Sphere)) at he
    change ‖finiteCoord (exteriorDiskNormalization d s hs (f (z : Sphere)))‖<1
    rw [←he,finiteCoord_coe]
    exact mem_ball_zero_iff.mp hw
  have hgi : InjOn g A := by
    intro z hz w hw he
    apply OnePoint.coe_injective
    apply hnorm.bijOn.injOn (hzU hz) (hzU hw)
    obtain ⟨a,_,ha⟩ := hnorm.2.1 (hzU hz)
    obtain ⟨b,_,hb⟩ := hnorm.2.1 (hzU hw)
    change finiteCoord ((exteriorDiskNormalization d s hs ∘ f) (z : Sphere))=
      finiteCoord ((exteriorDiskNormalization d s hs ∘ f) (w : Sphere)) at he
    rw [←ha,←hb,finiteCoord_coe,finiteCoord_coe] at he
    rw [←ha,←hb,he]
  have hbdy {x:ℂ} (hx:x∈K) : x∈closure A := by
    have hxn : x∉jordanInterior H := by
      change x∈frontier (jordanInterior H) at hx
      rw [(jordanInterior_isOpen H).frontier_eq] at hx
      exact hx.2
    simpa only [A,closure_compl,interior_closure_jordanInterior,mem_compl_iff] using hxn
  obtain ⟨_,he⟩ := analytic_jordan_closed_exterior_extension hH hs hf
  change EqOn E g A at he
  have hKb : MapsTo E K (closure (ball (0:ℂ) 1)) := by
    intro x hx
    rw [closure_ball (0:ℂ) one_ne_zero]
    apply mem_closedBall_zero_iff.mpr
    exact (analytic_jordan_closed_exterior_boundary_norm hH hs hf hx).le
  have hEi : InjOn E K := by
    apply injOn_boundary_of_holomorphic_extensions hgi hKb
    intro x hx
    obtain ⟨O,G,hO,hxO,hGd,hGi,hGe,hside⟩ := analytic_jordan_boundary_germ hH hs hf hx
    have hEG : E x=G x := extendFrom_eq_local_extension hO hGd.continuousOn hGe ⟨hxO,hbdy hx⟩
    exact ⟨O,G,hO,hxO,hGd,hGi,hEG.symm,hGe,fun z hz hzB =>
      (hside z hz).mp (mem_ball_zero_iff.mp hzB)⟩
  have hbd {x:ℂ} (hx:x∈closure A) (hxn:x∉A) : x∈K := by
    have hxcl : x∈closure (jordanInterior H) := not_not.mp hxn
    have hxout : x∉jordanInterior H := by
      simpa only [A,closure_compl,interior_closure_jordanInterior,mem_compl_iff] using hx
    change x∈frontier (jordanInterior H)
    rw [(jordanInterior_isOpen H).frontier_eq]
    exact ⟨hxcl,hxout⟩
  intro x hx y hy hexy
  by_cases hxA : x∈A
  · by_cases hyA : y∈A
    · apply hgi hxA hyA
      rwa [he hxA,he hyA] at hexy
    · have hxn : ‖E x‖<1 := by rw [he hxA];exact hu x hxA
      have hyn : ‖E y‖=1 := analytic_jordan_closed_exterior_boundary_norm hH hs hf (hbd hy hyA)
      rw [hexy,hyn] at hxn
      exact (lt_irrefl _ hxn).elim
  · by_cases hyA : y∈A
    · have hyn : ‖E y‖<1 := by rw [he hyA];exact hu y hyA
      have hxn : ‖E x‖=1 := analytic_jordan_closed_exterior_boundary_norm hH hs hf (hbd hx hxA)
      rw [←hexy,hxn] at hyn
      exact (lt_irrefl _ hyn).elim
    · exact hEi (hbd hx hxA) (hbd hy hyA) hexy

end CircleDomainRigidity

end

end OAI
